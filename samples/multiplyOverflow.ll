; ModuleID = 'multiplyOverflow.smt2'
source_filename = "multiplyOverflow.smt2"

define i1 @SMT(i32 %a, i32 %b) {
b1:
  %0 = zext i32 %b to i64
  %1 = zext i32 %a to i64
  %2 = mul i64 %1, %0
  %3 = lshr i64 %2, 32
  %4 = trunc i64 %3 to i32
  %5 = icmp eq i32 %4, 0
  %6 = xor i1 %5, true
  %7 = udiv i32 -1, %a
  %8 = icmp eq i32 %a, 0
  %9 = select i1 %8, i32 -1, i32 %7
  %10 = icmp uge i32 %9, %b
  %11 = and i1 %6, %10
  ret i1 %11
}
