import measure_theory.lebesgue_measure
import tactic

noncomputable theory

open measure_theory

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure :  probability_measure volume)

namespace probability_space
variables {α : Type*} [probability_space α]

lemma volume_univ : volume (set.univ : set α) = 1 :=
is_probability_measure.measure_univ

lemma volume_le_one (S : set α) : volume S ≤ 1 :=
by rw ← @volume_univ α; exact measure_mono (set.subset_univ _)

def prob (S : set α) : ℝ := (volume S).to_real

def nnprob (S : set α) : nnreal := (volume S).to_nnreal

theorem volume_eq_nnprob (S : set α) : volume S = nnprob S :=
(ennreal.coe_to_nnreal $ ne_top_of_le_ne_top (by rintro ⟨⟩) (volume_le_one S)).symm

theorem prob_eq_nnprob (S : set α) : prob S = nnprob S := rfl

theorem nnprob_le_one (S : set α) : nnprob S ≤ 1 :=
ennreal.coe_le_coe.1 $ by rw ← volume_eq_nnprob; exact volume_le_one S

theorem prob_le_one (S : set α) : prob S ≤ 1 := nnprob_le_one _

theorem zero_le_prob (S : set α) : 0 ≤ prob S := nnreal.zero_le_coe

theorem nnprob_mono {S T : set α} (h : S ⊆ T) : nnprob S ≤ nnprob T :=
ennreal.coe_le_coe.1 $ by simpa only [← volume_eq_nnprob] using measure_mono h

theorem prob_mono {S T : set α} (h : S ⊆ T) : prob S ≤ prob T :=
nnreal.coe_le_coe.2 $ nnprob_mono h

end probability_space

theorem measurable.map_probability_measure {α β} [probability_space α] [measurable_space β]
  {f : α → β} (hf : measurable f) :
  probability_measure (measure.map f volume) :=
⟨by rw measure_theory.measure.map_apply hf is_measurable.univ;
    exact probability_space.volume_univ⟩

-- In probability theory, a measurable function on a probability space is known as a random variable.
-- https://en.wikipedia.org/wiki/Measurable_function

structure random_variable (α β : Type*) [probability_space α] [measurable_space β] :=
(outcome : α → β)
(is_measurable_outcome : measurable outcome)

variables {α β : Type*} [probability_space α] [measurable_space β]

namespace random_variable
instance : has_coe_to_fun (random_variable α β) := ⟨_,outcome⟩
variable (X : random_variable α β)
lemma measurable : measurable X := X.is_measurable_outcome

-- distribution of X
def induced (X : random_variable α β) : probability_space β :=
{ volume := measure.map X volume,
  is_probability_measure := X.measurable.map_probability_measure }

variables [preorder β]

-- distribution function of X
def CDF (x : β) : 
  ℝ := @probability_space.prob _ X.induced {c | c ≤ x}

lemma prob_eq_CDF (x : β) : X.CDF x = @probability_space.prob β X.induced {c | c ≤ x} := rfl

theorem zero_le_CDF (x : β) : 0 ≤ X.CDF x := 
begin
  rw prob_eq_CDF,
  exact (@probability_space.zero_le_prob β X.induced {c : β | c ≤ x}),
end
 
theorem CDF_le_one (x : β) : X.CDF x ≤ 1 := 
begin
  rw prob_eq_CDF,
  exact (@probability_space.prob_le_one β X.induced {c : β | c ≤ x}),
end

-- distribution function of X with codomain correctly restricted to [0,1]
def CDF_in_01 (x: β) : set.Icc (0 : ℝ) 1 := ⟨ X.CDF x, X.zero_le_CDF x, X.CDF_le_one x⟩

-- Example of a measurable codomain

variables [topological_space β] [order_closed_topology β] [opens_measurable_space β]

example (b : β) : is_measurable {c | c ≤ b} := is_closed.is_measurable is_closed_Iic

end random_variable
