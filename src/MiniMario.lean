import measure_theory.lebesgue_measure
noncomputable theory
open measure_theory
class probability_space (α : Type*) extends measure_space α := (is_probability_measure :  probability_measure volume)

namespace probability_space
variables {α : Type*} [probability_space α]
lemma volume_univ : volume (set.univ : set α) = 1 := is_probability_measure.measure_univ
lemma volume_le_one (S : set α) : volume S ≤ 1 := by rw ← @volume_univ α; exact measure_mono (set.subset_univ _)
def prob (S : set α) : ℝ := (volume S).to_real
end probability_space

theorem measurable.map_probability_measure {α β} [probability_space α] [measurable_space β] {f : α → β} (hf : measurable f) : probability_measure (measure.map f volume) :=
⟨by rw measure_theory.measure.map_apply hf is_measurable.univ; exact probability_space.volume_univ⟩

structure random_variable (α β : Type*) [probability_space α] [measurable_space β] := (outcome : α → β) (is_measurable_outcome : measurable outcome)
variables {α β : Type*} [probability_space α] [measurable_space β] 

namespace random_variable
instance : has_coe_to_fun (random_variable α β) := ⟨_,outcome⟩
variable (X : random_variable α β)
lemma measurable : measurable X := X.is_measurable_outcome
def distribution (X : random_variable α β) : probability_space β := { volume := measure.map X volume, is_probability_measure := X.measurable.map_probability_measure }
def distribution_function [preorder β] (x : β) : ℝ := @probability_space.prob _ X.distribution {c | c ≤ x}
end random_variable
