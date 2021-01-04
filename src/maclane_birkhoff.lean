import algebra.ring.basic
import data.zsqrtd.basic
import ring_theory.subring
import data.real.basic
import data.nat.parity
import data.pnat.basic
import data.int.parity
import algebra.algebra.subalgebra
import algebra.group.defs
import analysis.special_functions.pow
import data.real.irrational
import tactic

-- Garrett Birkhoff and Saunders Mac Lane: A survey of modern algebra, 4th ed

namespace ch1A

-- 1.1 Commutative Rings

-- Integral domain

#check integral_domain

-- An integral domain of interest for number theory consists of all a + b √ 2, a and b ∈ ℤ 

#check ℤ√2

-- 1.2. Elementary Properties of Commutative Rings

universe u

variables {α : Type u} [comm_ring α] {a b c d z x₁ x₂ :  α}

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

theorem theorem_1 :
  (∀ a b c : α, c ≠ 0 → c*a = c*b → a = b) ↔
  (∀ a b : α, a ≠ 0 → b ≠ 0 → a * b ≠ 0) :=
begin
  split,
  { intros H a b ha hb ab,
    refine hb (H _ _ _ ha _),
    have hc := mul_zero a,
    rw hc,
    rw ab, 
  },
  { intros H a b c hc e,
    rw ← sub_eq_zero at e ⊢,
    refine by_contra (λ h, _),
    refine H c (a - b) hc h _,
    have hd := left_distrib c a (-b),
    have he := sub_eq_add_neg a b,
    rw ← he at hd,
    have hf := norm_num.mul_pos_neg c b (c * b) rfl,
    rw hf at hd,
    have hg := sub_eq_add_neg (c*a) (c*b),
    rw ← hg at hd,
    rw hd,
    exact e,
  },
end

#check left_distrib c a (-b)
/- A subdomain of an integral domain D is a subset of D
which is also an integral domain, for the same operations of addition and
multiplication. -/

variables {R : Type*} [integral_domain R] {D : subring R}
example : integral_domain D := subring.subring.domain D

-- Exercises for section 1.2

lemma ex1a : (a+b)*(c+d) = (a*c+b*c) + (a*d + b*d) := 
begin
  ring,
end

lemma ex1b1 : a+(b+(c+d))=(a+b)+(c+d) := 
begin
  ring,
end

lemma ex1b2 : (a+b)+(c+d)=((a+b)+c)+d := 
begin
  ring,
end

lemma ex1c : a+(b+c) = (c+a)+b:= 
begin
  ring,
end

lemma ex1d : a*(b*c)=c*(a*b) := 
begin
  ring,
end

lemma ex1e : a*(b+(c+d))=(a*b+a*c)+a*d := 
begin
  ring,
end

lemma ex1f : (a+b)*(c+d) = (a*c+b*c) + (a*d + b*d) := 
begin
  ring,
end

#check rule_8

lemma ex2b : 1*1=1 :=
begin
  ring,
end

/- Exercise 2c.  The only idempotents of an integral domain are 0 and 1. -/
variables {β : Type u} [integral_domain β] {x : β}
lemma ex2c : ∀ (x : β), x*x = x → (x = 0 ∨ x = 1) :=
begin
  intro x,
  intro h1,
  conv_rhs at h1 { rw ← mul_one x, },
  have h2 := sub_eq_zero.mpr h1,
  rw (mul_sub x x 1).symm at h2,
  have h3 := mul_eq_zero.mp h2,
  by_cases h4 : x = 0,
  by_cases h5 : x-1 = 0,
  exact or.inl h4,
  exact or.inl h4,
  refine or.inr _,
  exact (mul_right_inj' h4).mp h1,
end

lemma ex2c_JC (h1 : x * x = x) : x = 0 ∨ x = 1 := -- Johan Commelin
by simp [← @sub_eq_zero β _ _ 1, ← mul_eq_zero, mul_sub, h1]

lemma ex2c_KL {x : β} (h1 : x * x = x) : x = 0 ∨ x = 1 := -- Kenny Lau
or_iff_not_imp_left.2 $ λ hx, mul_left_cancel' hx $ h1.trans (mul_one x).symm

lemma ex3a : -(-a) = a :=
begin
  ring,
end

lemma ex3b : -(0 : α ) = 0 := 
begin
  ring,
end

lemma ex3c : -(a+b) = (-a) + (-b) := 
begin
  ring,
end

lemma ex3d : -a = (-1)*a := 
begin
  ring,
end

lemma ex3e1 : (-a)*b=a*(-b) := 
begin
  ring,
end

lemma ex3e2 : a*(-b)=-(a*b) := 
begin
  ring,
end

#check rule_9

lemma ex4 : (-1)*(-1) = (1:α) :=
begin
  ring,
end

end ch1A

namespace ch1B

universe u
variables {α : Type u} [integral_domain α] {a b c d : α}

lemma ex5a: (a-b) + (c-d) = (a+c)-(b+d) :=
begin
  ring,
end

lemma ex5b : (a-b)-(c-d) = (a+d)-(b+c) :=
begin
  ring,
end

lemma ex5c : (a-b)*(c-d) = (a*c + b*d)-(a*d+b*c)  :=
begin
  ring,
end

lemma ex5d : a-b=c-d ↔ a+d=b+c :=
begin
  split,
  {
    intro h,
    apply_fun (λ t, t+b+d) at h,
    conv at h 
    begin
      to_lhs,
      rw sub_add_cancel,
    end,
    conv at h
    begin
      to_rhs,
      rw sub_add_eq_add_sub,
      rw sub_add,
      rw sub_self,
      rw sub_zero,
    end,
    have swap := add_comm c b,
    rw swap at h,
    assumption,   
  },
  {
    intro h,
    apply_fun (λ t, t-b-d) at h,
    conv at h
    begin
      to_lhs,
      rw ← sub_add_eq_add_sub,
      rw ← add_sub,
      rw sub_self,
      rw add_zero,
    end,
    conv at h
    begin
      to_rhs,
      rw ← sub_add_eq_add_sub,
      rw sub_self,
      rw zero_add,
    end,
    assumption,
  },
end

lemma ex5e : (a-b)*c = a*c - b*c :=
begin
  ring,
end

instance (x : ℤ) : decidable (even x) :=  
  decidable_of_iff' _ even_iff_two_dvd

theorem ex6a :  ¬ ∃ s : subring ℤ, ∀ x, x ∈ s ↔ even x := -- Mario Carneiro
λ ⟨S, h⟩, absurd ((h 1).1 S.one_mem) dec_trivial

theorem ex6b :  ¬ ∃ s : subring ℤ, ∀ x, x ∈ s ↔ odd x :=
begin
  intro h1,
  cases h1 with S h,
  have h2 := h 0,
  have h3 := h2.1,
  have h4 := S.zero_mem,
  have h5 := h3 h4,
  have h6 := (@int.odd_iff_not_even 0).1,
  have h7 := h6 h5,
  have h8 := absurd h7 dec_trivial,
  exact h8,
end

theorem ex6c :  ¬ ∃ s : subring ℤ, ∀ x, x ∈ s ↔ (0:ℤ) < x := 
begin
  intro h1,
  cases h1 with S h,
  have h2 := h (0:ℤ),
  have h3 := subring.zero_mem S,
  have h4 := h2.1,
  have h5 := h4 h3,
  have h6 := lt_irrefl (0:ℤ),
  exact h6 h5,
end


-- Mario Carneiro
theorem ex6d : ¬ ∃ s : subring ℝ, ∀ x : ℝ, x ∈ s ↔ ∃ a b : ℤ, x = a + b * 5 ^ (1/4:ℝ) :=
begin
  rintro ⟨S, h⟩,
  simp only [one_div] at h,
  have hY : (5 ^ (2⁻¹:ℝ) : ℝ) = (5 ^ (4⁻¹:ℝ) : ℝ) * (5 ^ (4⁻¹:ℝ) : ℝ),
    by rw ← real.rpow_add; norm_num,
  have hX : (5 : ℝ) = (5 ^ (2⁻¹:ℝ) : ℝ) * (5 ^ (2⁻¹:ℝ) : ℝ),
    by rw ← real.rpow_add; norm_num,
  set X := (5 ^ (2⁻¹:ℝ):ℝ) with eX,
  have : X ∈ S,
  { have : (5 ^ (4⁻¹:ℝ) : ℝ) ∈ S := (h _).2 ⟨0, 1, by simp⟩,
    have := S.mul_mem this this,
    rwa hY },
  rcases (h _).1 this with ⟨a, b, e⟩, clear this,
  rw ← sub_eq_iff_eq_add' at e,
  have := congr (congr_arg (*) e) e,
  rw [mul_mul_mul_comm, ← hY, sub_mul, mul_sub, ← hX, ← sub_eq_zero] at this,
  have : X * (2 * a + b * b : ℤ) = (5 + a * a : ℤ),
  { symmetry, simp [← sub_eq_zero], refine eq.trans (by ring) this },
  by_cases h0 : ((2 * a + b * b : ℤ) : ℝ) = 0,
  { simp [h0] at this, linarith only [mul_self_nonneg ((a:ℤ):ℝ), this] },
  rw ← eq_div_iff h0 at this,
  refine (irrational_iff_ne_rational _).1 _ _ _ this,
  rw ← show real.sqrt 5 = X, by rw [eX, real.sqrt_eq_rpow, one_div],
  exact_mod_cast nat.prime.irrational_sqrt (by norm_num : nat.prime 5),
end

def ab54root := {x : ℝ // ∃ (a b : ℤ), x = a + b*5^(1/4)}
def ab94root := {x : ℝ // ∃ (a b : ℤ), x = a + b*9^(1/4)}
def binrat := {x : ℚ // ∃ (p : ℕ), x.denom = 2 ^ p }



end ch1B

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

