import algebra.ring.basic
import tactic

universe u

variables {α : Type u} [comm_ring α] {a b c z x₁ x₂ :  α}

/- Theorem 1. The cancellation law of multiplication for integral domains
is equivalent in a commutative ring to the assertion that 
a product of nonzero factors is not 0. -/

lemma lemma_1_LR: (c ≠ 0 → c*a = c*b → a = b)  → (a ≠ 0 → b ≠ 0 → a * b ≠ 0) :=
begin
  intro h1,
  intro h2,
  intro h3,
  intro h4,
  by_cases h5 : c ≠ 0,
  have h6 := h1 h5,
  by_cases h7 : c * a = c * b,
  have h8 := h6 h7,
  sorry,
  sorry,
  sorry,
end

lemma lemma_1_RL: (a ≠ 0 → b ≠ 0 → a * b ≠ 0) → (c ≠ 0 → c*a = c*b → a = b)  :=
begin
  intro h1,
  intro h2,
  intro h3,
  by_cases h4 : a ≠ 0,
  have h5 := h1 h4,
  by_cases h6 : c*a = c*b,
  by_cases h7 : b ≠ 0,
  have h8 := h5 h7,
  sorry,
  sorry,
  sorry,
  sorry,
end

theorem theorem_1 : (c ≠ 0 → c*a = c*b → a = b) ↔ (a ≠ 0 → b ≠ 0 → a * b ≠ 0) :=
begin
  split,
  exact lemma_1_LR,
  exact lemma_1_RL,
end
