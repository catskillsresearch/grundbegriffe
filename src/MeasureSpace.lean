import measure_theory.measurable_space
import measure_theory.measure_space


-- Measure space (S,Σ,μ)

instance M1_MS : measure_space M1 :=
{ to_measurable_space := M1,
  volume := M1_measure }


instance M1_MS : measure_space M1 :=
{ to_measurable_space := M1,
  volume := M1_measure }


instance M1_MS : measure_space M1 :=
{ to_measurable_space := M1_eq,
  volume := M1_measure }

The documentation is confusing because at the top level it says this:

structure measure_theory.measure_space (α : Type u_1) : Type u_1
to_measurable_space : measurable_space α
volume : measure_theory.measure α
I read this as meaning that I should supply an instance with two fields, to_measurable_space and volume. However, if I look at the source, it says something different:

class measure_space (α : Type*) extends measurable_space α :=
(volume : measure α)
I read this as meaning that I have to do everything I did for a measurable_space, and also supply a volume. In that case, based on example above in this thread:

instance : measure_space X :=
{ is_measurable' := A1,
  is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp, sorry ,
  volume := M1_measure
measure_theory.real.measure_space
measure_theory.measure.prod.measure_space

The first one is declared as

instance real.measure_space : measure_space ℝ :=
⟨{to_outer_measure := lebesgue_outer,
  m_Union := λ f hf, lebesgue_outer.Union_eq_of_caratheodory $
    λ i, borel_le_lebesgue_measurable _ (hf i),
  trimmed := lebesgue_outer_trim }⟩
and the second one as:

instance prod.measure_space {α β} [measure_space α] [measure_space β] : measure_space (α × β) :=
{ volume := volume.prod volume }
So real.measure_space supplies values for fields to_outer_measure and m_Union and trimmed, none of which are mentioned in the class definitions of measurable_space and subclass measure. prod.measure_space supplies a value for volume but nothing for
is_measurable' ,   is_measurable_empty,  is_measurable_compl and is_measurable_Union.

-- Creating a field to_measurable_space is how extends measurable_space works. Ideally the documentation could detect this and turn it back into extends for display purposes, but I'm not sure how easy that is in general.

instance M1_MS : measure_space M1 :=
{ to_measurable_space := M1,
  volume := M1_measure }
