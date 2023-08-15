; ModuleID = 'multiplyOverflow.smt2'
source_filename = "multiplyOverflow.smt2"

define i1 @SMT(i32 %a, i32 %b) {
b1:
  ret i1 false
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.umul.with.overflow.i32(i32, i32) #0

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
