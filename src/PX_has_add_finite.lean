import data.finset.basic
def X := fin 3
def plus (x y : set X) : set X := (x ∪ y : set X)
instance PX_has_add : has_add (set X):= ⟨ plus ⟩ 
#check PX_has_add -- X_has_add : has_add X
