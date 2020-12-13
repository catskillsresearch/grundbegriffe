import data.finset.basic

namespace finite_monoid_example

def X : set ℕ := ({1, 2, 3} : finset ℕ)
def mul (x y : set X) : set X := (x ∩ y : set X)
instance : has_mul (set X) := ⟨ mul ⟩
lemma mul_assoc (x y z : set X) : (x * y) * z = x * (y * z) := inf_assoc
instance : has_one (set X) := ⟨ set.univ ⟩ 
lemma one_mul (a : set X) : 1 * a = a := top_inf_eq
lemma mul_one (a : set X): a * 1 = a := inf_top_eq

instance : monoid (set X) :=
{
  one := 1,
  mul := (*),
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one
}

end finite_monoid_example
