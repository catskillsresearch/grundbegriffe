import algebra.ring.basic
import algebra.algebra.subalgebra
import algebra.group.defs
import analysis.special_functions.pow
import data.nat.parity
import data.nat.prime
import data.pnat.basic
import data.int.parity
import data.zmod.basic
import data.rat.basic
import data.real.basic
import data.real.irrational
import data.zsqrtd.basic
import ring_theory.subring
import tactic
import tactic.slim_check
import data.equiv.ring
import algebra.punit_instances
open rat
open nat
open tactic
open real

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

/- Set s is closed under addition and multiplication, so if

a b c d : ℤ
x = a + b * 9 ^ (1/4:ℝ)
y = c + d * 9 ^ (1/4:ℝ)

then

x + y = (a+c) + (b +d)* 9 ^ (1/4:ℝ)
(a+c): ℤ
(b+d): ℤ
hence

(x+y)∈ s
and

9 ^ (1/4:ℝ) *9 ^ (1/4:ℝ) =(3:ℤ)
and

x *y=(a*c+b*d*3)+(a*d+b*c)* 9 ^ (1/4:ℝ)
(a*c+b*d*3): ℤ
(a*d+b*c): ℤ
hence

(x*y)∈ s
and hence

s : subring ℝ -/
-- Eric Wieser
/-- The image of `zsqrtd` in `ℝ`.  -/
@[simps]
noncomputable def zsqrtd.to_real {d : ℤ } (h : 0 ≤ d) : ℤ√d →+* ℝ := {
  to_fun := λ a, a.1 + a.2*real.sqrt d,
  map_zero' := by simp,
  map_add' := λ a b, by { simp, ring, },
  map_one' := by simp,
  map_mul' := λ a b, by {
    have : (↑a.re + ↑a.im * real.sqrt d) * (↑b.re + ↑b.im * real.sqrt d) =
             ↑a.re * ↑b.re + (↑a.re * ↑b.im + ↑a.im * ↑b.re) * real.sqrt d
                           + ↑a.im * ↑b.im * (real.sqrt d * real.sqrt d) := by ring,
    simp [this, real.mul_self_sqrt (int.cast_nonneg.mpr h)],
    ring, } }

-- Eric Wieser
abbreviation is_an_integral_domain {α : Type*} [ring α] (s : set α) := ∃ (sr : subring α) [integral_domain sr], s = sr

lemma nine_equals_3_times_3 : (9:ℝ)=(3:ℝ)*(3:ℝ) :=
begin
  linarith,
end

lemma three_is_gt_0 : (0:ℝ) < (3:ℝ) :=
begin
  linarith,
end

lemma three_is_gte_0 : (0:ℝ) ≤ (3:ℝ) :=
begin
  linarith,
end

lemma sqrt_of_9_is_3 : (3:ℝ) = (real.sqrt (9:ℝ)) :=
begin
  have h1 := nine_equals_3_times_3,
  rw h1,
  have h2 := three_is_gte_0,
  have h3 := real.sqrt_mul_self h2,
  rw ← h1 at h3,
  rw ← h1,
  exact eq.symm h3,
end

lemma half_plus_half_equals_1: (1/2:ℝ)+(1/2:ℝ)=1 :=
begin
  linarith,
end

lemma x_equals_sqrtx_times_sqrtx (x:ℝ): 0 < x → x = x^(1/2:ℝ) * x^(1/2:ℝ) :=
begin
  intro h1,
  have h2 := real.rpow_add h1,
  have h3 := h2 (1/2) (1/2),
  have h4 := half_plus_half_equals_1,
  rw h4 at h3,
  have h5 := real.rpow_one x,
  rw h5 at h3,
  exact h3,
end

lemma x_is_0 (x:ℝ) : x ≥ 0 → ¬(0 < x) → x = 0 :=
begin
  intro h1,
  intro h2,
  linarith,
end

lemma half_ne_0 : (1/2:ℝ)  ≠ (0:ℝ) :=
begin
  linarith,
end

lemma zero_le_0 : (0:ℝ) ≤ (0:ℝ) :=
begin
  linarith,
end

lemma sqrt_0_equals_0 : real.sqrt 0 = 0 :=
begin
  have h1 := zero_le_0,
  exact real.sqrt_eq_zero_of_nonpos h1,
end

lemma x_gt_0_implies_sqrt_x_gt_0 (x:ℝ): x ≥ 0 → x^(1/2:ℝ) ≥ 0 :=
begin
  intro h1,
  exact real.rpow_nonneg_of_nonneg h1 (1 / 2),
end

lemma sqrt_x_equals_sqrt_x (x:ℝ) : x ≥ 0 → x^(1/2:ℝ) = real.sqrt x :=
begin
  intro h,
  have h1 := x_equals_sqrtx_times_sqrtx x,
  by_cases h2 : 0 < x,
  {
    have h3 := h1 h2,
    conv
    begin
      to_rhs,
      rw h3,
    end,
    have h5 := x_gt_0_implies_sqrt_x_gt_0 x,
    have h6 := h5 h,
    have h4 := real.sqrt_mul_self h6,
    exact eq.symm h4, 
  },
  {
    have h3 := x_is_0 x,
    have h4 := h3 h,
    have h5 := h4 h2,
    rw h5,
    have h6 := @real.zero_rpow (1/2:ℝ),
    have h7 := half_ne_0,
    have h8 := h6 h7,
    rw h8,
    have h9 := sqrt_0_equals_0,
    exact eq.symm h9,
  }
end

lemma x_mul_x_pow_y_equals_x_pow_y_plus_y (x y : ℝ) : 0 < x → (x * x)^y = x^(y+y) :=
begin
  intro h,
  have h1 := le_of_lt h,
  have h2 := @real.mul_rpow x x y h1 h1,
  rw h2,
  have h3 := real.rpow_add h y y,
  exact eq.symm h3,  
end

lemma fourth_root_of_9_equals_sqrt_sqrt : (9:ℝ) ^ (1/4:ℝ) = real.sqrt (real.sqrt (9:ℝ)) :=
begin
  have h1 := nine_equals_3_times_3,
  have h2 := three_is_gt_0,
  have h7 := three_is_gte_0,
  have h3 := sqrt_of_9_is_3,
  rw ← h3,
  rw h1,
  have h4 := sqrt_x_equals_sqrt_x (3:ℝ),
  have h5 := h4 h7,
  rw ← h5,
  have h6 := x_mul_x_pow_y_equals_x_pow_y_plus_y 3 (1/4),
  have h8 := h6 h2,
  rw h8,
  ring,
end

lemma fourth_root_of_nine_equals_sqrt_3 : (9:ℝ) ^ (1/4:ℝ) = real.sqrt 3 := 
begin 
  have h1 := fourth_root_of_9_equals_sqrt_sqrt,
  rw h1,
  have h2 := sqrt_of_9_is_3,
  rw h2,
end

theorem ex6e : is_an_integral_domain {x : ℝ | ∃ a b : ℤ, x = a + b * (9:ℝ) ^ (1/4:ℝ)} :=
begin
  refine ⟨(zsqrtd.to_real (show 0 ≤ (3 : ℤ), by norm_num)).range, _, _⟩,
  apply_instance,
  ext,
  rw [fourth_root_of_nine_equals_sqrt_3],
  simp [zsqrtd.to_real],
  split,
  {
    intro h1,
    cases h1 with a ha,
    cases ha with b hb,
    use {re := a, im := b},
    rw hb,
  },
  {
    intro h1,
    cases h1 with y hy,
    rw ← hy,
    use [y.re, y.im],
  }
end

lemma useful : ((9 : ℝ) ^ (4⁻¹ : ℝ)) * (9 ^ (4⁻¹ : ℝ)) = 3 :=
begin
  rw ← mul_rpow,
  convert pow_nat_rpow_nat_inv (show (0 : ℝ) ≤ 3, by norm_num) (show 0 < 4, by norm_num) using 2,
  all_goals {norm_num}
end

def A : subring ℝ :=
{ carrier := {x | ∃ a b : ℤ, x = a + b * (9:ℝ) ^ (1/4:ℝ)},
  one_mem' := ⟨1, 0, by simp⟩,
  mul_mem' := begin
    rintro _ _ ⟨a1, b1, rfl⟩ ⟨a2, b2, rfl⟩,
    use [a1 * a2 + 3 * b1 * b2, a1 * b2 + a2 * b1],
    simp [mul_add, add_mul, mul_assoc, mul_left_comm, useful],
    ring,
  end,
  zero_mem' := ⟨0, 0, by simp⟩,
  add_mem' := by { rintro _ _ ⟨a1, b1, rfl⟩ ⟨a2, b2, rfl⟩,
                   use [a1 + a2, b1 + b2],
                   simp, ring },
  neg_mem' := by { rintro _ ⟨a, b, rfl⟩,
                   use [-a, -b],
                   simp, ring },
   }

theorem ex6e_kevin_buzzard : is_an_integral_domain {x : ℝ | ∃ a b : ℤ, x = a + b * (9:ℝ) ^ (1/4:ℝ)} :=
⟨A, infer_instance, rfl⟩

theorem ex6e_mario_carneiro : is_an_integral_domain {x : ℝ | ∃ a b : ℤ, x = a + b * (9:ℝ) ^ (1/4:ℝ)} :=
begin
  refine ⟨(zsqrtd.to_real (show 0 ≤ (3 : ℤ), by norm_num)).range, _, _⟩,
  apply_instance,
  ext,
  rw calc (9:ℝ) ^ (1/4:ℝ) = (9:ℝ)^((2:ℕ)⁻¹ * (1/2) : ℝ) : by norm_num
    ... = ((3^2:ℝ)^((2:ℕ)⁻¹:ℝ)) ^ (1/2:ℝ) : by rw real.rpow_mul; norm_num
    ... = real.sqrt 3 : by rw [real.pow_nat_rpow_nat_inv, real.sqrt_eq_rpow]; norm_num,
  simp [zsqrtd.to_real],
  exact ⟨λ ⟨x,y,h⟩, ⟨⟨x,y⟩, h.symm⟩, λ ⟨⟨x,y⟩,h⟩, ⟨x,y, h.symm⟩⟩,
end

-- Exercise 6F

-- Mario Carneiro, Hanting Zhang
lemma eq_two_pow_of_dvd_two_pow {a n : ℕ} : a ∣ 2 ^ n → ∃ m : ℕ, a = 2 ^ m := 
begin
  intro h1,
  have h2 := (@dvd_prime_pow 2 nat.prime_two n a).1 h1,
  cases h2 with m hm,
  cases hm with H hH,
  finish,
end

lemma succ_def (m: ℕ) : m.succ = m + 1 := rfl

lemma pow_two_ne_zero (n : ℕ): 2^n ≠ 0 :=
begin
  induction n with d hd,
  simp,
  rw (succ_def d),
  rw (pow_succ 2 d),
  simp,
  intro h,
  finish,
end 

-- Mario Carneiro
lemma plus_injective {a b : ℚ} {n m : ℕ} (ha : a.denom = 2 ^ n) (hb : b.denom = 2 ^ m) :
  ∃ k : ℕ, (a + b).denom = 2 ^ k :=
begin
  apply @eq_two_pow_of_dvd_two_pow _ (n + m),
  rw [rat.add_num_denom, ← int.coe_nat_mul, ha, hb, ← pow_add, ← int.coe_nat_dvd],
  apply rat.denom_dvd,
end 

-- Mario Carneiro
lemma mul_injective {a b : ℚ} {n m : ℕ} (ha : a.denom = 2 ^ n) (hb : b.denom = 2 ^ m) :
  ∃ k : ℕ, (a * b).denom = 2 ^ k :=
begin
  apply @eq_two_pow_of_dvd_two_pow _ (n + m),
  rw [rat.mul_num_denom, ha, hb, ← pow_add, ← int.coe_nat_dvd],
  apply rat.denom_dvd,
end

noncomputable def B : subring ℚ :=
{ 
  carrier := {x : ℚ | ∃ n : ℕ, x.denom = 2 ^ n },
  one_mem' /- (1 : M) ∈ carrier) -/ := 
  begin
    rw set.mem_set_of_eq,
    use 0,
    simp,
  end,
  mul_mem' /- {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier) -/ := 
  begin
    intros a b h1 h2,
    rw set.mem_set_of_eq at h1,
    rw set.mem_set_of_eq at h2,
    cases h1 with n hn,
    cases h2 with m hm,
    rw set.mem_set_of_eq,
    exact (mul_injective hn hm),
  end,
  zero_mem' /- (0 : M) ∈ carrier -/ := 
  begin
    rw set.mem_set_of_eq,
    use 0,
    simp,
    exact rfl,
  end,
  add_mem' /- {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier -/:= 
  begin
    intro a,
    intro b,
    intro h1,
    intro h2,
    rw set.mem_set_of_eq at h1,
    rw set.mem_set_of_eq at h2,
    cases h1 with n hn,
    cases h2 with m hm,
    rw set.mem_set_of_eq,
    exact (plus_injective hn hm),
  end,
  neg_mem' /- {x} : x ∈ carrier →d -x ∈ carrier -/:= 
  begin
    intro x,
    intro h1,
    rw set.mem_set_of_eq at h1,
    cases h1 with n hn,
    rw set.mem_set_of_eq,
    use n,
    simp,
    exact hn,
  end,
 }

theorem ex6f : is_an_integral_domain {x : ℚ | ∃ n : ℕ, x.denom = 2 ^ n }  :=
⟨B, infer_instance, rfl⟩

inductive R
| zero
| one

open R

def R.add : R → R → R
| zero zero := zero
| zero one := one
| one zero := one
| one one := zero

def R.mul : R → R → R
| zero zero := zero
| zero one := zero
| one zero := zero
| one one := one

def R.neg : R → R
| zero := zero
| one := one

instance : has_add R := ⟨R.add⟩
instance : has_mul R := ⟨R.mul⟩
instance : has_zero R := ⟨zero⟩
instance : has_one R := ⟨one⟩
instance : has_neg R := ⟨R.neg⟩

theorem R.exists_pair_ne : ∃ (x y : R), x ≠ y :=
begin
   use [R.zero, R.one],
end

theorem R.zero_add (a : R): 0 + a = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.add_zero (a : R): a + 0 = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.one_mul (a : R): 1 * a = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.mul_one (a : R): a * 1 = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.add_assoc (a b c : R): a + b + c = a + (b + c) := 
begin
   cases a,
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
end

theorem R.add_left_neg (a : R): -a + a = 0 := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.add_comm (a b : R): a + b = b + a := 
begin
   cases a,
   cases b,
   repeat { exact rfl },
   cases b,
   repeat { exact rfl },
end

theorem R.mul_assoc (a b c : R): a * b * c = a * (b * c) := 
begin
   cases a,
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
end


theorem R.left_distrib (a b c : R): a * (b + c) = a * b + a * c := 
begin
   cases a,
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
end

theorem R.right_distrib (a b c : R): (a + b) * c = a * c + b * c := 
begin
   cases a,
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
   cases b,
   cases c,
   repeat { exact rfl },
   cases c,
   repeat { exact rfl },
end

theorem R.mul_comm (a b : R): a * b = b * a := 
begin
   cases a,
   cases b,
   repeat { exact rfl },
   cases b,
   repeat { exact rfl },
end

theorem R.eq_zero_or_eq_zero_of_mul_eq_zero (a b : R) (h: a * b = 0): a = 0 ∨ b = 0:=
begin
   cases a,
   cases b,
   left,
   exact rfl,
   left,
   exact rfl,
   cases b,
   right,
   exact rfl,
   exfalso,
   finish,   
end

instance ex7a_kyle_miller : integral_domain R :=
{
  zero := R.zero,
  one := R.one,
  add := R.add,
  mul := R.mul,
  add_assoc := R.add_assoc,
  zero_add := R.zero_add,
  add_zero := R.add_zero,
  neg := R.neg,
  add_left_neg := R.add_left_neg,
  add_comm := R.add_comm,
  one_mul := R.one_mul,
  mul_assoc := R.mul_assoc,
  mul_one := R.mul_one ,
  left_distrib := R.left_distrib,
  right_distrib := R.right_distrib,
  mul_comm := R.mul_comm,
  exists_pair_ne := R.exists_pair_ne,
  eq_zero_or_eq_zero_of_mul_eq_zero := R.eq_zero_or_eq_zero_of_mul_eq_zero,
}

instance : fact (nat.prime 2) := nat.prime_two

-- this is `@field.to_integral_domain _ (zmod.field 2)` under the hood
instance ex7a_eric_wieser : integral_domain (zmod 2) := by apply_instance

namespace ex7b

inductive R
| zero

open R

def R.add : R → R → R
| zero zero := zero

def R.mul : R → R → R
| zero zero := zero

def R.neg : R → R
| zero := zero

instance : has_add R := ⟨R.add⟩
instance : has_mul R := ⟨R.mul⟩
instance : has_zero R := ⟨zero⟩
instance : has_neg R := ⟨R.neg⟩

theorem R.zero_add (a : R): 0 + a = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.add_zero (a : R): a + 0 = a := 
begin
   cases a,
   repeat { exact rfl },
end

theorem R.add_assoc (a b c : R): a + b + c = a + (b + c) := 
begin
  cases a,
  cases b,
  cases c,
  refl,
end

theorem R.add_left_neg (a : R): -a + a = 0 := 
begin
   cases a,
   refl,
end

theorem R.add_comm (a b : R): a + b = b + a := 
begin
   cases a,
   cases b,
   refl,
end

theorem R.mul_assoc (a b c : R): a * b * c = a * (b * c) := 
begin
   cases a,
   cases b,
   cases c,
   refl,
end


theorem R.left_distrib (a b c : R): a * (b + c) = a * b + a * c := 
begin
   cases a,
   cases b,
   cases c,
   refl,
end

theorem R.right_distrib (a b c : R): (a + b) * c = a * c + b * c := 
begin
   cases a,
   cases b,
   cases c,
   refl,
end

theorem R.mul_comm (a b : R): a * b = b * a := 
begin
   cases a,
   cases b,
   refl,
end

theorem R.eq_zero_or_eq_zero_of_mul_eq_zero (a b : R) (h: a * b = 0): a = 0 ∨ b = 0:=
begin
  cases a,
  cases b,
  left,
  refl,
end

end ex7b

lemma ex8a_eric_wieser {S: Type*} [CR: comm_ring S] 
        [NZD: no_zero_divisors S] (h : (0 : S) = 1) : S ≃+* unit :=
begin
  refine ring_equiv.symm _,
  refine {to_fun := _, inv_fun := _, left_inv := _, right_inv := _, map_mul' := _, map_add' := _},
  intro h,
  exact ring.one,
  intro h1,
  exact (),
  rw function.left_inverse,
  intro x,
  exact unit.ext,
  rw function.right_inverse,
  rw function.left_inverse,
  intro x,
  exact eq_of_zero_eq_one h ring.one x,
  intro u1,
  intro u2,
  ring,
  exact eq_of_zero_eq_one h ring.one (ring.one * ring.one),
  intro u1,
  intro u2,
  exact eq_of_zero_eq_one h ring.one (ring.one + ring.one),
end

def is_zero_ring (α : Type u) [ring α] : Prop := ∀ (x : α), x = 0

lemma ex8a_kyle_miller (S : Type u) [comm_ring S] [no_zero_divisors S] :
  is_integral_domain S ∨ is_zero_ring S :=
begin
  by_cases h: (1:S) ≠ (0:S),
  fconstructor,
  refine {exists_pair_ne := _, mul_comm := _, eq_zero_or_eq_zero_of_mul_eq_zero := _},
  use [0,1],
  refine ne_comm.mp _,
  assumption,
  exact mul_comm,
  exact λ {a b : S}, mul_eq_zero.mp,
  refine or.inr _,
  rw is_zero_ring,
  refine eq_zero_of_zero_eq_one _,
  finish,
end


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

