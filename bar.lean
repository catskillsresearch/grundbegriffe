import measure_theory.lebesgue_measure
import measure_theory.borel_space
import data.set.intervals.basic
import measure_theory.measure_space

open measure_theory

noncomputable instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

abbreviation I01 := (set.Icc (0 : ℝ) 1)

instance : probability_measure (volume : measure I01) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume I01 = 1, {simpa},
    rw [real.volume_Icc], simp
  end }
