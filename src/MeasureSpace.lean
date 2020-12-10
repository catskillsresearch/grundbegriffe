import measure_theory.measure_space
import Measure

open measure_theory

noncomputable theory

-- Measure space (S,Σ,μ)

-- Example 1 : 𝒫 ⊤

#check M1
#check μ_M1
#check measure_space

noncomputable def M1_MS : measure_space X := {
  to_measurable_space := M1,
  volume := μ_M1 }

#check M1_MS -- M1_MS : measure_space X

-- Example 2 : {⊤ , ∅}

#check M2
#check μ_M2

noncomputable def M2_MS : measure_space X := {
  to_measurable_space := M2,
  volume := μ_M2 }

-- What are the pieces? 

#check X -- carrier set
#reduce X -- {0,1,2}

#check A2 -- σ algebra
#reduce A2

#check XA2 -- proof that A2 is a σ algebra
#reduce XA2

#check M2 -- proof that (X,A2) is a measurable space
#reduce M2

#check μ_M2 -- proof that 
-- #reduce μ_M2 --- timeout
#check μ_M2.

#check M2_MS -- proof that (X,A2) is a measure space
-- #reduce M2_MS -- timeout
#check M2_MS.volume
-- #reduce M2_MS.volume

-- Example 3: B(ℝ)

#check measure_theory.measure_space.volume
#check measure_theory.real.measure_space
#check (volume : measure ℝ) -- Lebesgue measure on ℝ 

-- Example 4: B([0,1])

-- define
-- instance subtype.measure_space
-- using coercion and

#check measure_theory.measure.comap