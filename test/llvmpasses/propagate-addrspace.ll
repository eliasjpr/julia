; RUN: opt -load libjulia.so -PropagateJuliaAddrspaces -die -S %s | FileCheck %s

define i64 @simple() {
; CHECK-LABEL: @simple
; CHECK-NOT: addrspace(11)
    %stack = alloca i64
    %casted = addrspacecast i64 *%stack to i64 addrspace(11)*
    %loaded = load i64, i64 addrspace(11)*%casted
    ret i64 %loaded
}
