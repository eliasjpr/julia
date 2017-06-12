// This file is a part of Julia. License is MIT: https://julialang.org/license

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Analysis/CFG.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/ValueMap.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Pass.h>
#include <llvm/Support/Debug.h>

#include "llvm-version.h"
#include "codegen_shared.h"
#include "julia.h"

#define DEBUG_TYPE "propagate_julia_addrspaces"

using namespace llvm;

/* This pass performs propagation of addrspace information that is legal from
   the frontend definition, but illegal by general IR semantics. In particular,
   this includes:
      - Changing the address space of a load/store if the base pointer is
        in an untracked address space
      - Commuting GEPs and addrspace casts

    This is most useful for removing superflous casts that can inhibit LLVM
    optimizations.
*/

struct PropagateJuliaAddrspaces : public FunctionPass, public InstVisitor<PropagateJuliaAddrspaces> {
    static char ID;
    DenseMap<Value *, Value *> LiftingMap;
    SmallPtrSet<Value *, 4> Visited;
    std::vector<Instruction *> ToDelete;
    PropagateJuliaAddrspaces() : FunctionPass(ID) {};

public:
    bool runOnFunction(Function &F) override;
    Value *LiftPointer(Value *V, Type *LocTy = nullptr, Instruction *InsertPt=nullptr);
    void visitStoreInst(StoreInst &SI);
    void visitLoadInst(LoadInst &LI);
    void visitMemSetInst(MemSetInst &MI);
    void visitMemTransferInst(MemTransferInst &MTI);
};

bool PropagateJuliaAddrspaces::runOnFunction(Function &F) {
    visit(F);
    for (Instruction *I : ToDelete)
        I->eraseFromParent();
    ToDelete.clear();
    LiftingMap.clear();
    Visited.clear();
    return true;
}

static unsigned getValueAddrSpace(Value *V) {
    return cast<PointerType>(V->getType())->getAddressSpace();
}

static bool isSpecialAS(unsigned AS) {
    return AddressSpace::FirstSpecial <= AS && AS <= AddressSpace::LastSpecial;
}

Value *PropagateJuliaAddrspaces::LiftPointer(Value *V, Type *LocTy, Instruction *InsertPt) {
    SmallVector<Value *, 4> Stack;
    Value *CurrentV = V;
    // Follow pointer casts back, see if we're based on a pointer in
    // an untracked address space, in which case we're allowed to drop
    // intermediate addrspace casts.
    while (true) {
        Stack.push_back(CurrentV);
        if (isa<BitCastInst>(CurrentV))
            CurrentV = cast<BitCastInst>(CurrentV)->getOperand(0);
        else if (isa<AddrSpaceCastInst>(CurrentV)) {
            CurrentV = cast<AddrSpaceCastInst>(CurrentV)->getOperand(0);
            if (!isSpecialAS(getValueAddrSpace(CurrentV)))
                break;
        }
        else if (isa<GetElementPtrInst>(CurrentV)) {
            if (LiftingMap.count(CurrentV)) {
                CurrentV = LiftingMap[CurrentV];
                break;
            } else if (Visited.count(CurrentV)) {
                return nullptr;
            }
            CurrentV = cast<GetElementPtrInst>(CurrentV)->getOperand(0);
            Visited.insert(CurrentV);
        } else
            break;
    }
    if (!CurrentV->getType()->isPointerTy())
        return nullptr;
    if (isSpecialAS(getValueAddrSpace(CurrentV)))
        return nullptr;
    // Ok, we're allowed to change the address space of this load, go back and
    // reconstitute any GEPs in the new address space.
    for (Value *V : llvm::reverse(Stack)) {
        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V);
        if (!GEP)
            continue;
        if (LiftingMap.count(GEP)) {
            CurrentV = LiftingMap[GEP];
            continue;
        }
        GetElementPtrInst *NewGEP = cast<GetElementPtrInst>(GEP->clone());
        NewGEP->insertBefore(GEP);
        Type *GEPTy = GEP->getSourceElementType();
        NewGEP->setSourceElementType(GEPTy);
        SmallVector<Value *, 4> Operands;
        auto it = GEP->op_begin(); ++it; // skip pointer operand
        for (;it != GEP->op_end(); ++it) {
            Operands.push_back(*it);
        }
        NewGEP->mutateType(GetElementPtrInst::getGEPReturnType(GEPTy, CurrentV, Operands));
        if (cast<PointerType>(CurrentV->getType())->getElementType() != GEPTy)
            CurrentV = new BitCastInst(CurrentV, GEPTy->getPointerTo(), "", NewGEP);
        NewGEP->setOperand(GetElementPtrInst::getPointerOperandIndex(), CurrentV);
        LiftingMap[GEP] = NewGEP;
        CurrentV = NewGEP;
    }
    if (LocTy && cast<PointerType>(CurrentV->getType())->getElementType() != LocTy) {
        CurrentV = new BitCastInst(CurrentV, LocTy->getPointerTo(), "", InsertPt);
    }
    return CurrentV;
}

void PropagateJuliaAddrspaces::visitLoadInst(LoadInst &LI) {
    unsigned AS = LI.getPointerAddressSpace();
    if (!isSpecialAS(AS))
        return;
    Value *Replacement = LiftPointer(LI.getPointerOperand(), LI.getType(), &LI);
    if (!Replacement)
        return;
    LI.setOperand(LoadInst::getPointerOperandIndex(), Replacement);
}

void PropagateJuliaAddrspaces::visitStoreInst(StoreInst &SI) {
    unsigned AS = SI.getPointerAddressSpace();
    if (!isSpecialAS(AS))
        return;
    Value *Replacement = LiftPointer(SI.getPointerOperand(), SI.getValueOperand()->getType(), &SI);
    if (!Replacement)
        return;
    SI.setOperand(StoreInst::getPointerOperandIndex(), Replacement);
}

void PropagateJuliaAddrspaces::visitMemSetInst(MemSetInst &MI) {
    unsigned AS = MI.getDestAddressSpace();
    if (!isSpecialAS(AS))
        return;
    Value *Replacement = LiftPointer(MI.getRawDest());
    if (!Replacement)
        return;
    Value *TheFn = Intrinsic::getDeclaration(MI.getModule(), Intrinsic::memset,
        {Replacement->getType(), MI.getOperand(1)->getType()});
    CallInst *CI = CallInst::Create(TheFn, {Replacement, MI.getOperand(1)}, "", &MI);
    CI->takeName(&MI);
#if JL_LLVM_VERSION >= 50000
    CI->copyMetadata(MI);
#else
    SmallVector<std::pair<unsigned, MDNode *>, 4> TheMDs;
    MI.getAllMetadataOtherThanDebugLoc(TheMDs);
    for (const auto &MD : TheMDs)
        CI->setMetadata(MD.first, MD.second);
    CI->setDebugLoc(MI.getDebugLoc());
#endif
    ToDelete.push_back(&MI);
}

void PropagateJuliaAddrspaces::visitMemTransferInst(MemTransferInst &MTI) {
    unsigned DestAS = MTI.getDestAddressSpace();
    unsigned SrcAS = MTI.getSourceAddressSpace();
    if (!isSpecialAS(DestAS) && !isSpecialAS(SrcAS))
        return;
    Value *Dest = MTI.getRawDest();
    if (isSpecialAS(DestAS)) {
        Value *Replacement = LiftPointer(Dest, cast<PointerType>(Dest->getType())->getElementType(), &MTI);
        if (Replacement)
            Dest = Replacement;
    }
    Value *Src = MTI.getRawSource();
    if (isSpecialAS(SrcAS)) {
        Value *Replacement = LiftPointer(Src, cast<PointerType>(Src->getType())->getElementType(), &MTI);
        if (Replacement)
            Src = Replacement;
    }
    if (Dest == MTI.getRawDest() && Src == MTI.getRawSource())
        return;
    Value *TheFn = Intrinsic::getDeclaration(MTI.getModule(), MTI.getIntrinsicID(),
        {Dest->getType(), Src->getType(),
         MTI.getOperand(2)->getType()});
    CallInst *CI = CallInst::Create(TheFn, {Dest, Src,
        MTI.getOperand(2), MTI.getOperand(3), MTI.getOperand(4)},
        "", &MTI);
    CI->takeName(&MTI);
    #if JL_LLVM_VERSION >= 50000
        CI->copyMetadata(MTI);
    #else
        SmallVector<std::pair<unsigned, MDNode *>, 4> TheMDs;
        MTI.getAllMetadataOtherThanDebugLoc(TheMDs);
        for (const auto &MD : TheMDs)
            CI->setMetadata(MD.first, MD.second);
        CI->setDebugLoc(MTI.getDebugLoc());
    #endif
    ToDelete.push_back(&MTI);
}

char PropagateJuliaAddrspaces::ID = 0;
static RegisterPass<PropagateJuliaAddrspaces> X("PropagateJuliaAddrspaces", "Propagate (non-)rootedness information", false, false);

Pass *createPropagateJuliaAddrspaces() {
    return new PropagateJuliaAddrspaces();
}
