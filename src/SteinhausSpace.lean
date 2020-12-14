import measure_theory.lebesgue_measure
open measure_theory
noncomputable theory

instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure:  probability_measure volume)

instance Steinhaus_measure : probability_measure (volume : measure (set.Icc (0 : ℝ) 1)) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume (set.Icc (0 : ℝ) 1) = 1, {simpa},
    rw [real.volume_Icc], simp
  end 
}

instance Steinhaus_space : probability_space (set.Icc (0 : ℝ) 1) := 
{ is_probability_measure := Steinhaus_measure }
