import algebra.group.defs
import data.finset.basic
import data.nat.basic

def X := fin 3
instance X_nontrivial : nontrivial X := fin.nontrivial
#check X_nontrivial --X_nontrivial : nontrivial X

instance X_has_add : has_add (fin 3):= fin.has_add
#check X_has_add -- X_has_add : has_add X

instance X_add_semigroup : add_semigroup ℕ := nat.add_semigroup
#check X_add_semigroup -- X_add_semigroup : add_semigroup ℕ

@[reducible]
def A := set (fin 3)
#check A
#reduce A

def plus (x y : A) := x ∪ y

instance : has_add ( finset ℕ  ) := ⟨ λ x y, x ∪ y ⟩

def X : set ℕ := ({1, 2, 3} : finset ℕ)
#check X -- X : set ℕ
#reduce X -- λ (x : ℕ), x = 1 ∨ x = 2 ∨ x = 3 ∨ false

def A := set X
#check A -- A : set (set ℕ)
#reduce A -- λ (t : ℕ → Prop), ∀ ⦃a : ℕ⦄, t a → a = 1 ∨ a = 2 ∨ a = 3 ∨ false

def plus (x y : A) : A := (x ∪ y : set X)
example (x y : A) : A := set.union x y -- alternative

instance : has_add A := ⟨ plus ⟩