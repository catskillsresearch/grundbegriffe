import data.real.ennreal
import measure_theory.measure_space

-- Measure μ: A→ [0,∞)

def finite_set_measure_of(X: Type): SubSet X → ennreal := λ F, size X F

def M1_measure : measure M1 := finite_set_measure_of X



def M1_measure : measure M1 := finite_set_measure_of X

noncomputable def M1_measure : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)


instance : fintype X := fin.fintype _
noncomputable instance foo (s : set X) : fintype s := by classical; apply_instance

noncomputable def M1_measure : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

instance : fintype X := fin.fintype _
noncomputable instance foo (s : set X) : fintype s := by classical; apply_instance

noncomputable def M1_measure : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

