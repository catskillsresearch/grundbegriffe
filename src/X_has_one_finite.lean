import data.finset.basic

namespace has_one_finite_fin_3
def X := fin 3
instance : nontrivial X := fin.nontrivial
instance : has_one X := fin.has_one
end has_one_finite_fin_3

namespace has_one_finite_finset_123
def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X_one : X := ⟨1,set.mem_insert 1 (λ (b : ℕ), b = 2 ∨ list.mem b [3])⟩
instance : has_one X := { one := X_one }
end has_one_finite_finset_123