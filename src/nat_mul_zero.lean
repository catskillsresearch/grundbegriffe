import algebra.group_with_zero.defs

namespace version_1

instance : mul_zero_class ℕ  := {
  mul := nat.has_mul.mul,
  zero := 0,
  zero_mul := nat.zero_mul,
  mul_zero := nat.mul_zero,
}

end version_1

namespace version_2

import data.nat.basic
set_option trace.class_instances true
#check (by apply_instance : mul_zero_class ℕ)

end version_2