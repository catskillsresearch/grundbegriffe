
import measure_theory.lebesgue_measure

open measure_theory

noncomputable theory

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure:  probability_measure volume)

class random_variable (α β : Type*) :=
(domain : probability_space α )
(codomain : measurable_space β )
(outcome : α → β)
(is_measurable_outcome : @measurable α  β domain codomain outcome)
