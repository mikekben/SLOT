; ModuleID = "frontend.py"
target triple = "unknown-unknown-unknown"
target datalayout = ""

declare half @"llvm.fabs.f16"(half %".1")

declare float @"llvm.fabs.f32"(float %".1")

declare double @"llvm.fabs.f64"(double %".1")

declare half @"llvm.fma.f16"(half %".1", half %".2", half %".3")

declare float @"llvm.fma.f32"(float %".1", float %".2", float %".3")

declare double @"llvm.fma.f64"(double %".1", double %".2", double %".3")

declare half @"llvm.sqrt.f16"(half %".1")

declare float @"llvm.sqrt.f32"(float %".1")

declare double @"llvm.sqrt.f64"(double %".1")

declare i1 @"llvm.is.fpclass.f16"(half %".1", i32 %".2")

declare i1 @"llvm.is.fpclass.f32"(float %".1", i32 %".2")

declare i1 @"llvm.is.fpclass.f64"(double %".1", i32 %".2")

declare half @"llvm.minnum.f16"(half %".1", half %".2")

declare float @"llvm.minnum.f32"(float %".1", float %".2")

declare double @"llvm.minnum.f64"(double %".1", double %".2")

declare half @"llvm.maxnum.f16"(half %".1", half %".2")

declare float @"llvm.maxnum.f32"(float %".1", float %".2")

declare double @"llvm.maxnum.f64"(double %".1", double %".2")

define i1 @"smt"(i32 %"a", i32 %"b")
{
.4:
  %".5" = zext i32 %"a" to i64
  %".6" = zext i32 %"b" to i64
  %".7" = mul i64 %".5", %".6"
  %".8" = lshr i64 %".7", 32
  %".9" = trunc i64 %".8" to i32
  %".10" = icmp eq i32 %".9", 0
  %".11" = xor i1 %".10", -1
  %".12" = icmp eq i32 %"a", 0
  %".13" = udiv i32 4294967295, %"a"
  %".14" = select  i1 %".12", i32 -1, i32 %".13"
  %".15" = icmp uge i32 %".14", %"b"
  %".16" = and i1 %".11", %".15"
  ret i1 %".16"
}
