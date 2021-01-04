import algebra.algebra.subalgebra
import data.real.basic

theorem ℝ_1_is_unique :
  ∀ (u : ℝ), (∀ (x : ℝ), u * x = x ∧ x * u = x) → u=1 :=
begin
  intro h1,
  intro h2,
  sorry,
end

theorem ℝ_0_is_unique :
  ∀ (z : ℝ),
    (∀ (x : ℝ),
      z + x = x ∧ 
      x + z = x ∧ 
      (∀ (y : ℝ), x * y = z → (x = z ∨ y = z)))
    → z=0 := 
begin
  intro h1,
  intro h2,
  sorry,
end

def ℤ_even := {x : ℤ | ∃ y, x = 2 * y}

theorem ℤ_even_is_not_a_submonoid: ¬ is_submonoid ℤ_even := 
begin
  intro h,
  sorry,
end

theorem ℤ_even_is_not_an_integral_domain_because_missing_1 : 
  ¬(∃ (u ∈ ℤ_even), 
    ∀ (x ∈ ℤ_even),
    u * x = x ∧ 
    x * u = x) := 
begin
  intro h1,
  sorry,
end

def yadda : set ℕ := {(1:ℕ),2}

class is_golem (s : set ℕ) : Prop :=
(three_mem : (3:ℕ) ∈ s)



#check @is_golem yadda

theorem yadda_not_golem : ¬ (is_golem yadda) :=
begin
  intro h,
  
end

