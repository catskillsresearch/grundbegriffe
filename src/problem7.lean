import analysis.special_functions.pow
import data.real.irrational

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

theorem ex6e : ∃ s : subring ℝ, ∀ x : ℝ, x ∈ s ↔ ∃ a b : ℤ, x = a + b * 9 ^ (1/4:ℝ) :=
begin
  apply exists.intro,
  intro x,
  split,
  {
    intro h1,
    apply exists.intro,
    apply exists.intro,
    sorry,
    exact int.one,
    exact int.one,
  },
  {
    intro h1,
    cases h1 with a ha,
    cases ha with b hb,
    refine (subring.mem_mk' _ _).mpr rfl,
    rotate,
    rotate,
    exact is_unit.submonoid ℝ,
    exact add_subgroup.center ℝ,
    rotate,
    rotate,
    sorry,
    sorry,
    sorry,
    sorry,
  },
end

theorem ex6f : ∃ s : subring ℚ, ∀ x : ℚ, x ∈ s ↔ ∃ n : ℕ, x.denom = 2 ^ n :=
begin
  apply exists.intro,
  intro h,
  split,
  {
    intro h1,
    apply exists.intro,
    sorry,
    sorry,
  },
  {
    intro h1,
    cases h1 with n hn,
    exact subring.mem_top h,
  },
end
