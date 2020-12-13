import data.finset.basic
def X : set ℕ := ({1, 2, 3} : finset ℕ)
def mul (x y : set X) : set X := (x ∩ y : set X)
instance X_has_mul : has_mul (set X) := ⟨ mul ⟩
theorem X_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance X_semigroup : semigroup (set X) := ⟨ mul, X_mul_assoc ⟩