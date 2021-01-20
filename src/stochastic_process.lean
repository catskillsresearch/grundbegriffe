import measure_theory.lebesgue_measure
import measure_theory.measurable_space

open measure_theory

-- https://en.wikipedia.org/wiki/Probability_space

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure:  probability_measure volume)

-- https://en.wikipedia.org/wiki/Random_variable#Definition

def random_variable (α β: Type*) (PS: probability_space α) (MS: measurable_space β):=
  @measurable α β PS.to_measure_space.to_measurable_space MS

--https://en.wikipedia.org/wiki/Stochastic_process#Stochastic_process

def stochastic_process (α β T: Type*) (PS: probability_space α) (MS: measurable_space β) (X: T → α → β) (t: T) := 
  random_variable α β PS MS (X t)

-- https://en.wikipedia.org/wiki/Stochastic_process#Index_set

def index_set (α β T: Type*) (X: T → α → β) := T

-- https://en.wikipedia.org/wiki/Stochastic_process#State_space

def state_space (α β T: Type*) (X: T → α → β) := β

-- https://en.wikipedia.org/wiki/Stochastic_process#Sample_function

def sample_function (α β T: Type*) (X: T → α → β) := λ (ω: α), λ (t: T), X t ω 

-- https://en.wikipedia.org/wiki/Stochastic_process#Law
def law (α β T: Type*) 
        (PS: probability_space α) 
        (MS: measurable_space β) 
        (X: T → α → β) 
        (t: T) 
        (SP: stochastic_process α β T PS MS X t)
        (HM: has_mem β β)
        (Y: set β):=
  PS.volume.to_outer_measure.measure_of {ω : α | ∃ y:β, X t ω ∈ y}

-- Steinhaus space

noncomputable instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

instance steinhaus_measure : probability_measure (volume : measure (set.Icc (0 : ℝ) 1)) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume (set.Icc (0 : ℝ) 1) = 1, {simpa},
    rw [real.volume_Icc], simp
  end 
}

noncomputable instance steinhaus_space : probability_space (set.Icc (0 : ℝ) 1) := 
{ is_probability_measure := steinhaus_measure }