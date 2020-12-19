import measure_theory.lebesgue_measure
import measure_theory.measure_space

open measure_theory
noncomputable theory

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure :  probability_measure volume)

def probability_space.distribution (α : Type*) [ps: probability_space α] :=
  ps.volume

structure random_variable (α β : Type*) [probability_space α] [measurable_space β] :=
(outcome : α → β)
(is_measurable_outcome : measurable outcome)

variables {α β : Type} [probability_space α] [measurable_space β] 

instance distribution_space  (X : random_variable α β) : probability_space β :=
{ volume := measure.map X.outcome volume,
  is_probability_measure := begin
    constructor,
    rw measure_theory.measure.map_apply X.is_measurable_outcome is_measurable.univ,
    apply probability_space.is_probability_measure.measure_univ,
  end }

instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

namespace Steinhaus

instance P : probability_measure (volume : measure (set.Icc (0 : ℝ) 1)) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume (set.Icc (0 : ℝ) 1) = 1, {simpa},
    rw [real.volume_Icc], simp
  end }

instance ΩAP : probability_space (set.Icc (0 : ℝ) 1) := 
{ is_probability_measure := Steinhaus.P }

#check Steinhaus.ΩAP.volume -- volume : measure ↥(set.Icc 0 1)

end Steinhaus


--def distribution_function  (X : random_variable α ℝ ) (DS: distribution_space X)