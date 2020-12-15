import algebra.group_with_zero.defs
import tactic

namespace finite_powerset_mul_zero_example

def X := fin 3
def mul (x y : set X) : set X := (x ∩ y : set X)
instance has_mul : has_mul (set X) := ⟨ mul ⟩ 
instance has_zero : has_zero (set X) := ⟨ ∅ ⟩ 
lemma zero_mul (a : set X): 0 * a = 0 := bot_inf_eq
lemma mul_zero (a : set X): a * 0 = 0 := inf_bot_eq

instance : mul_zero_class (set X) := {
  mul := has_mul.mul,
  zero := ∅,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
} 

end finite_powerset_mul_zero_example