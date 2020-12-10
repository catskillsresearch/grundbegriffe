import data.real.ennreal
import measure_theory.measure_space
import MeasurableSpace

-- Measure μ: A → [0,∞)

-- Example 0

instance inhabitant : fintype (fin 1) := fin.fintype 1

def A :=  λ a, a ∈ (𝒫 ⊤ : set (set (fin 1)))

def M : measurable_space (fin 1) := { is_measurable_empty := by {rw A, finish},
  is_measurable' := A,
  is_measurable_compl := assume a h, by {rw A at *, finish},
  is_measurable_Union := assume f hf, by {rw A at *, simp },
}

noncomputable abbreviation qlbrdl (s: set (fin 1)) (z: @is_measurable (fin 1) M s) : ennreal := 
  finset.card s.to_finset

noncomputable def μ : @measure_theory.measure (fin 1) M :=
@measure_theory.measure.of_measurable _ M
  (qlbrdl)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

-- Example 1

instance witness : fintype X := fin.fintype 3

noncomputable def μ_M1 : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

-- Example 2

noncomputable def μ_M2 : @measure_theory.measure X M2 :=
@measure_theory.measure.of_measurable _ M2
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin simp, sorry end)
