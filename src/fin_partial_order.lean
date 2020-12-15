import data.nat.basic

instance fin_n_partial_order (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

lemma fin_n_partial_order1 (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

def fin_n_partial_order2 (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

example : (∀ n : ℕ , partial_order (fin n)) :=
begin
  intro h,
  exact subtype.partial_order (λ (i : ℕ), i < _),
end

#check (by apply_instance : ∀ n, partial_order (fin n))