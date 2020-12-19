import measure_theory.lebesgue_measure
open measure_theory
noncomputable theory

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure :  probability_measure volume)

namespace probability_space

lemma volume_univ {α : Type*} [probability_space α] : volume (set.univ : set α) = 1 :=
  is_probability_measure.measure_univ

def prob {α : Type*} [probability_space α] {S : set α} (h : is_measurable S) : ennreal :=
  volume S

end probability_space

structure random_variable (α β : Type*) [probability_space α] [measurable_space β] :=
(outcome : α → β)
(is_measurable_outcome : measurable outcome)

variables {α β : Type*} [probability_space α] [measurable_space β]

namespace random_variable
instance : has_coe_to_fun (random_variable α β) := ⟨_,outcome⟩
lemma measurable (X : random_variable α β) : measurable X := X.is_measurable_outcome

def induced (X : random_variable α β) : probability_space β :=
{ volume := measure.map X volume,
  is_probability_measure := begin
    constructor,
    erw measure_theory.measure.map_apply X.measurable is_measurable.univ,
    exact probability_space.volume_univ
  end }

def distribution_function (X : random_variable α ℝ) : ℝ → ennreal := λ x,
  @probability_space.prob _ X.induced {c | c ≤ x} is_measurable_Iic

structure is_measurable_with_le (β: Type*) (b: β) [measurable_space β] [preorder β] :=
 (proof: is_measurable {c: β | c ≤ b})

def generalized_distribution_function (α β : Type*) [probability_space α] [mb: measurable_space β] 
          [po: preorder β] (X: random_variable α β) (b: β) [im: @is_measurable_with_le β b mb po]  := 
    @probability_space.prob β X.induced {c | c ≤ b} im.proof

end random_variable
