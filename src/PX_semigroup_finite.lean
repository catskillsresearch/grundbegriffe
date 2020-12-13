import data.finset.basic
-- def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X := fin 3
def PX_mul (x y : set X) : set X := (x ∩ y : set X)
instance PX_has_mul : has_mul (set X) := ⟨ PX_mul ⟩ 
theorem PX_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance PX_semigroup : semigroup (set X) := ⟨ PX_mul, PX_mul_assoc ⟩
