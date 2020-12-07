import measure_theory.measure_space
import Measure

open measure_theory

-- Measure space (S,Σ,μ)

-- Example 1

#check M1
#check μ_M1
#check measure_space

noncomputable def M1_MS : measure_space X := {
  to_measurable_space := M1,
  volume := μ_M1 }

#check M1_MS -- M1_MS : measure_space X

-- Example 2

#check M2
#check μ_M2

noncomputable def M2_MS : measure_space X := {
  to_measurable_space := M2,
  volume := μ_M2 }

#check M2_MS -- M2_MS : measure_space X