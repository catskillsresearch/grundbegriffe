import data.finset.basic

namespace finite_add_monoid_example

def X : set ℕ := ({1, 2, 3} : finset ℕ)

def plus (x y : set X) : set X := (x ∪ y : set X)
instance : has_add (set X) := ⟨ plus ⟩

instance : has_zero (set X) := ⟨ ∅ ⟩ 

lemma zero_add (a : set X) : 0 + a = a := bot_sup_eq

lemma add_zero (a : set X) : a + 0 = a := sup_bot_eq

lemma add_assoc ( a b c : set X) : a + b + c = a + (b + c) := sup_assoc

instance : add_monoid (set X) :=
{
  add := (+),
  zero := ∅,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
}

end finite_add_monoid_example
