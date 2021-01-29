import tactic
import tactic.slim_check
import algebra.ordered_ring
universe u

-- 1.3. Properties of Ordered Domains

-- closest match to Birkhoff-Mac Lane "ordered domain is"
#check linear_ordered_comm_ring -- Mario Carneiro

-- Exercises for section 1.3

theorem ex_1_3_1_a (α: Type u) [linear_ordered_comm_ring α] 
   (a b c : α) (h: a < b): a + c < b + c := 
  add_lt_add_right h c

theorem ex_1_3_1_b (α: Type u) [linear_ordered_comm_ring α] 
   (a x y : α): a-x < a-y ↔ x > y := sub_lt_sub_iff_left a

lemma lt0_lt_flip (α: Type*) [linear_ordered_ring α] -- Ruben Van de Velde
   (a x : α) (hx: a * x < 0) (ha: a < 0) : 0 < x :=
  pos_of_mul_neg_right hx ha.le

theorem ex_1_3_1_c (α: Type u) [linear_ordered_comm_ring α] 
   (a x y : α) (h: a < 0): a*x > a* y ↔ x < y :=
begin
  split,
  {
    intro h0,
    have h1 := sub_lt_zero.mpr h0,
    apply sub_lt_zero.1,
    rw ← mul_sub at h1,
    have h2 := lt0_lt_flip α a (y-x) h1 h,
    rw (neg_sub x y).symm at h2,
    exact neg_pos.1 h2,
  },
  {
    intro h0,
    apply sub_lt_zero.1,
    rw ← mul_sub,
    have h1 := sub_pos.2 h0,
    exact mul_neg_of_neg_of_pos h h1,
  }
end

theorem ex_1_3_1_d (α: Type u) [linear_ordered_comm_ring α] 
   (a b c : α) (ha: 0 < c) (hacbc: a*c < b*c): a < b :=
  (mul_lt_mul_right ha).mp hacbc

theorem ex_1_3_1_e (α: Type u) [linear_ordered_comm_ring α] 
   (x : α) (h: x + x + x + x = 0) : x = 0 :=
begin
  rw (add_assoc (x+x) x x) at h,
  exact bit0_eq_zero.mp (bit0_eq_zero.mp h),
end

lemma together  (α: Type u) [linear_ordered_comm_ring α] (a b: α) (h: a-b = 0)  : a = b := 
  sub_eq_zero.mp h

lemma factor_expr (α: Type u) [linear_ordered_comm_ring α] (a b : α) :
  a * (b ^ 2 * -3) + (a ^ 2 * (b * 3)) = 3*a*b*(a - b) :=
begin
  apply (together α (a * (b ^ 2 * -3) + (a ^ 2 * (b * 3))) (3*a*b*(a - b))),
  ring,
end

lemma move_cubes_left (α: Type u) [linear_ordered_comm_ring α]
   (a b : α) (h: 0 < a * (b ^ 2 * -3) + (a ^ 2 * (b * 3) + (-a ^ 3 + b ^ 3))) :
   a^3- b^3 < a * (b ^ 2 * -3) + (a ^ 2 * (b * 3)) :=
begin
  linarith,
end

lemma negneg (α: Type u) [linear_ordered_comm_ring α] (a b : α): a - b = - (b - a):=
begin
  linarith,
end

lemma this_is_negative (α: Type u) [linear_ordered_comm_ring α] (a b : α)
      (h1: 0 < b - a)
      (hha: a > 0)
      (hhb: b > 0) : 3 * a * b * (a - b) < 0 :=
begin
  rw negneg α a b,
  have h3 := zero_lt_three,
  have h4 := mul_pos h3 hha,
  have h5 := mul_pos h4 hhb,
  simp,
  have h6 := neg_lt_zero.mpr h1,
  have h7 := neg_sub b  a,
  rw h7 at h6,
  exact linarith.mul_neg h6 h5,
  exact nontrivial_of_lt 0 (b - a) h1,
end

lemma this_is_positive (α: Type u) [linear_ordered_comm_ring α] (a b : α)
      (h1: 0 < b - a) (hb: b > 0) (alt0: a < 0) : 0 < 3 * a * b * (a - b) :=
begin
  have h3 := zero_lt_three,
  have h4 := mul_neg_of_pos_of_neg h3 alt0,
  have h5 := mul_neg_of_neg_of_pos h4 hb,
  have h6 := neg_lt_zero.mpr h1,
  have h7 := mul_pos_of_neg_of_neg h5 h6,
  have h8 := neg_sub b a,
  rw h8 at h7,
  exact h7,
  exact nontrivial_of_lt 0 (b - a) h1,
end

lemma simp_pow (α: Type u) [linear_ordered_comm_ring α]: (0:α)^3 = 0 :=
  tactic.ring_exp.pow_p_pf_zero rfl rfl

lemma is_lt_0 (α: Type u) [linear_ordered_comm_ring α] (b : α)
      (hb: ¬b > 0) (hb0: ¬b = 0): b < 0 :=
  (ne.le_iff_lt hb0).mp (not_lt.mp hb)

lemma odd_pos_neg_neg (α: Type u) [linear_ordered_comm_ring α] (a : α)
        (h: a < 0) : a^3 < 0 :=
  pow_bit1_neg_iff.mpr h

lemma this_be_negative (α: Type u) [linear_ordered_comm_ring α] (a b : α)
      (h1: a < b)
      (halt0: a < 0)
      (hblt0: b < 0) : 
      3 * a * b * (a - b) < 0 :=
begin
  have h3 := zero_lt_three,
  have h4 := sub_lt_zero.mpr h1,
  have h5 := mul_pos_of_neg_of_neg  halt0 hblt0,
  have h6 := mul_pos h3 h5,
  have h7 := sub_lt_zero.mpr h1,
  have h8 := linarith.mul_neg h7 h6,
  finish,
  exact nontrivial_of_lt a b h1,
end

theorem ex_1_3_1_f (α: Type u) [linear_ordered_comm_ring α]
   (a b : α) (h: a < b): a^3 < b^3 :=
begin
  have h1 := sub_pos.2 h,
  have h2 := pow_pos h1 3,
  repeat { rw pow_succ' at h2, },
  simp at h2,
  rw sub_eq_neg_add at h2,
  repeat { rw right_distrib at h2, rw left_distrib at h2, },
  ring_exp at h2,
  have h3 := move_cubes_left α a b h2,
  rw factor_expr α a b at h3,
  by_cases ha : a > 0,
  {
    by_cases hb : b > 0,
    {
      have h4 := this_is_negative α a b h1 ha hb,
      have h5 := lt_trans h3 h4,
      exact sub_lt_zero.1 h5,
    },
    {
      exfalso,
      exact hb (lt_trans ha h),
    },
  },
  by_cases ha0: a = 0,
  {
    rw ha0 at *,
    simp at *,
    assumption,
  },
  {
    have halt0 := is_lt_0 α a ha ha0,
    have h3alt0 := odd_pos_neg_neg α a halt0,
    by_cases hb : b > 0,
    {
      have h3bgt0 := pow_pos hb 3,
      exact lt_trans h3alt0 h3bgt0,
    },
    by_cases hb0 : b = 0,
    {
      rw hb0,
      rw simp_pow,
      assumption,
    },
    {
      have hblt0 := is_lt_0 α b hb hb0,
      have hf := this_be_negative α a b h halt0 hblt0,
      have hf1 := lt_trans h3 hf,
      finish,
    }
  }
end

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

