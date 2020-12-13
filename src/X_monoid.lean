import data.finset.basic

def X := fin 3
def mul (x y : set X) : set X := (x ∩ y : set X)
instance X_has_mul : has_mul (set X) := ⟨ mul ⟩
instance X_has_one : has_one X := fin.has_one
theorem X_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance X_semigroup : semigroup (set X) := ⟨ mul, X_mul_assoc ⟩

#check X_has_one.one

instance X_monoid : monoid (set X) := 
{
    mul := X_has_mul.mul,
    one := X_has_one.one,
    mul_assoc := sorry,
    one_mul := sorry,
    mul_one := sorry,
}
