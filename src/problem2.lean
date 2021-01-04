import algebra.algebra.subalgebra

def ℤ_even := {x : ℤ | ∃ y, x = 2 * y}

instance : is_submonoid ℤ_even := {
  one_mem := sorry,
  mul_mem := sorry,
}

instance : is_add_submonoid ℤ_even := {
  add_mem := sorry,
  zero_mem := sorry,
}

instance : is_add_subgroup ℤ_even := {
  neg_mem := sorry,
}

instance : is_subring ℤ_even := {}

instance : integral_domain ℤ_even := @subring.domain ℤ _ ℤ_even _
