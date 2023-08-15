; ModuleID = 'rem.smt2'
source_filename = "rem.smt2"

define i1 @SMT(double %x, double %y, double %r) {
b:
  %0 = bitcast double %x to i64
  %1 = call double @llvm.experimental.constrained.fadd.f64(double %x, double %y, metadata !"round.tonearest", metadata !"fpexcept.ignore")
  %2 = bitcast double %1 to i64
  %3 = icmp eq i64 %0, %2
  %4 = call double @llvm.experimental.constrained.fadd.f64(double %x, double %y, metadata !"round.tonearest", metadata !"fpexcept.ignore")
  %5 = call i1 @llvm.is.fpclass.f64(double %4, i32 3)
  %6 = call i1 @llvm.is.fpclass.f64(double %x, i32 3)
  %7 = and i1 %6, %5
  %8 = or i1 %7, %3
  ret i1 %8
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare double @llvm.experimental.constrained.fadd.f64(double, double, metadata, metadata) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i1 @llvm.is.fpclass.f64(double, i32 immarg) #1

attributes #0 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
