import data.finset.basic

namespace finite_zero_example_fin_3
def X := fin 3
instance : has_zero X := fin.has_zero
end finite_zero_example_fin_3

namespace finite_zero_example_finset_012
def X : set ℕ := ({0,1,2} : finset ℕ)
def X_zero : X := ⟨0,set.mem_insert 0 (λ (b : ℕ), b = 1 ∨ list.mem b [2])⟩
instance : has_zero X := { zero := X_zero }
end finite_zero_example_finset_012

namespace finite_zero_example_set_fin3
def X := fin 3
instance : has_zero X := fin.has_zero
instance : has_zero (set X) := ⟨ ∅ ⟩ 
end finite_zero_example_set_fin3
