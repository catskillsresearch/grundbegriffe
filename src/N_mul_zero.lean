import algebra.group_with_zero.defs
instance : mul_zero_class ℕ  := {
  mul := nat.has_mul.mul,
  zero := 0,
  zero_mul := nat.zero_mul,
  mul_zero := nat.mul_zero,
}