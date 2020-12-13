import data.finset.basic
/- def X := fin 3

instance : nontrivial X := fin.nontrivial

instance PX_has_one : has_one (set X) :=
{ one := set.univ } -/

def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X_one : X := ⟨1,set.mem_insert 1 (λ (b : ℕ), b = 2 ∨ list.mem b [3])⟩
instance X_has_one : has_one X := { one := X_one }

def X_one' : set ℕ := ({1} : finset ℕ)

#check X_one -- X_one : ↥X
#reduce X_one -- ⟨1, _⟩

#check X_one' -- X_one' : set ℕ
#reduce X_one' -- λ (x : ℕ), x = 1 ∨ false

