import algebra.ring.basic
import data.zsqrtd.basic
import ring_theory.subring
import tactic

-- Garrett Birkhoff and Saunders Mac Lane: A survey of modern algebra, 4th ed

namespace ch1

-- 1.1 Commutative Rings

-- Integral domain

#check integral_domain

-- An integral domain of interest for number theory consists of all a + b √ 2, a and b ∈ ℤ 

#check ℤ√2

-- 1.2. Elementary Properties of Commutative Rings

universe u

variables {α : Type u} [comm_ring α] {a b c z x₁ x₂ :  α}

lemma rule_1 : (a+b)*c=a*c+b*c := add_mul _ _ _
lemma rule_2_plus : (0 + a = a) := zero_add _
lemma rule_2_times : (1 * a = a) := one_mul _

lemma rule_3 : (∀ (a : α), a + z = a) → z = 0 := 
begin
  intro h1,
  have h2 := h1 0,
  exact add_left_eq_self.mp (congr_arg (has_add.add z) (congr_arg (has_add.add z) (h1 z))),
end

lemma rule_4 : a + b = a + c → b = c := (add_right_inj a).mp

lemma rule_5 : a + x₁ = 0 → a + x₂ = 0 → x₁ = x₂ :=
begin
  intro h1,
  intro h2,
  exact neg_unique h1 h2,
end

lemma rule_6 : a + x₁ = b → a + x₂ = b → x₁ = x₂ :=
begin
  intro h1,
  intro h2,
  rw ← h1 at h2,
  exact rule_4 (eq.symm h2),
end

lemma rule_7a : a * 0 = 0 := mul_zero a
lemma rule_7b  : 0 * a = 0 := zero_mul a

lemma rule_8 : (∀ (a : α), a*z = a) → z = 1 :=
begin
  intro h1,
  exact (eq_one_iff_eq_one_of_mul_eq_one (h1 1)).mp rfl,
end

lemma rule_9 : (-a)*(-b) = a*b := neg_mul_neg _ _

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

/- A subdomain of an integral domain D is a subset of D
which is also an integral domain, for the same operations of addition and
multiplication. -/

variables {R : Type*} [integral_domain R] {D : subring R}
example : integral_domain D := subring.subring.domain D

-- Exercises for section 1.2

-- 1.3. Properties of Ordered Domains

-- Exercises for section 1.3

-- 1.4. Well-Ordering Principle

-- Exercises for section 1.4

-- 1.5. Finite Induction; Laws of Exponents

-- Exercises for section 1.5

-- 1.6. Divisibility

-- Exercises for section 1.6

-- 1.7. The Euclidean Algorithm

-- Exercises for section 1.7

-- 1.8. Fundamental Theorem of Arithmetic

-- Exercises for section 1.8

-- 1.9. Congruences

-- Exercises for section 1.9

-- 1.10. The Rings ℤn

-- Exercises for section 1.10

-- 1.11. Sets, Functions, and Relations

-- Exercises for section 1.11

-- 1.12. Isomorphisms and Automorphisms

-- Exercises for section 1.12

end ch1