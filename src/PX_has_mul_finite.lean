import data.finset.basic
def X := fin 3
def PX_mul (x y : set X) : set X := (x ∩ y : set X)
instance PX_has_mul : has_mul (set X) := ⟨ PX_mul ⟩ 

