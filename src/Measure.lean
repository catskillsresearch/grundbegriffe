import data.real.ennreal
import measure_theory.measure_space
import MeasurableSpace

-- Measure μ: A → [0,∞)

-- Example 1

instance XFT : fintype X := fin.fintype _
noncomputable instance foo (s : set X) : fintype s := by classical; apply_instance

#check X
#check XFT
#check A1
#check M1
#check measure

noncomputable def μ_M1 : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

#check μ_M1
#check μ_M1 -- measure_theory.measure X
#check @measure_theory.measure.trimmed X M1 μ_M1

-- Example 2

#check A2
#check M2

noncomputable def μ_M2 : @measure_theory.measure X M2 :=
@measure_theory.measure.of_measurable _ M2
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin simp, sorry end)

#check μ_M2
#check μ_M2 -- measure_theory.measure X
#check @measure_theory.measure.trimmed X M2 μ_M2