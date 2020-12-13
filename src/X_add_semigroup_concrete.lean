import data.finset.basic
def X := fin 3
def plus (x y : set X) : set X := (x ∪ y : set X)
instance X_has_add : has_add (set X) := ⟨ plus ⟩
theorem X_add_assoc (x y z : set X) :  (x + y) + z = x + (y + z) := sup_assoc
instance X_add_semigroup : add_semigroup (set X) := ⟨ plus, X_add_assoc ⟩ 