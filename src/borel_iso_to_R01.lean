import measure_theory.lebesgue_measure
import tactic

noncomputable theory

open measure_theory

universes u₁ u₂

#check measurable_space : measurable_space : Type u_1 → Type u_1

/- A measurable function is a function between the underlying sets of two measurable spaces that preserves 
the structure of the spaces: the preimage of any measurable set is measurable.
In probability theory, a measurable function on a probability space is known as a random variable.
https://en.wikipedia.org/wiki/Measurable_function -/

#check @measurable
/- measurable :
  Π {α : Type u_1} {β : Type u_2} [_inst_1 : measurable_space α] [_inst_2 : measurable_space β],
    (α → β) → Prop  -/

/- For a pairing between X and Y (where Y need not be different from X) to be a bijection, four properties must hold:
each element of X must be paired with at least one element of Y,
no element of X may be paired with more than one element of Y,
each element of Y must be paired with at least one element of X, and
no element of Y may be paired with more than one element of X.
https://en.wikipedia.org/wiki/Bijection -/

class bijection (X : Type u₁) (Y : Type u₂) (f: X → Y ) :=
(into: ∀ x : X, ∃ y : Y, f(x) = y)
(unique_into: ∀ y₁ y₂ : Y, ∀ x : X, f(x)=y₁ ∧ f(x)=y₂ → y₁ = y₂)
(onto: ∀ y : Y, ∃ x : X, f(x) = y)
(unique_onto: ∀ x₁ x₂ : X, ∀ y : Y, f(x₁)=y ∧ f(x₂)=y → x₁ = x₂)

#check borel_space -- borel_space : Π (α : Type u_1) [_inst_1 : topological_space α] [_inst_2 : measurable_space α], Prop

/- A Borel isomorphism is a measurable bijective function between two measurable standard Borel spaces
https://en.wikipedia.org/wiki/Borel_isomorphism -/

def borel_isomorphism  (X : Type u₁) (Y : Type u₂) 
              [TSX: topological_space X] [MSX: measurable_space]
              [TSY: topological_space Y] [MSY: measurable_space]
              (f: X → Y ) 
              [BSX: borel_space X] [BSY: borel_space Y] 
              [measurable f] [bijection f] := true

def R01 := set.Icc (0:ℝ) 1

theorem R01_is_topological_space : topological_space R01 := sorry

theorem R01_is_measurable_space: measurable_space R01 := sorry

theorem R01_is_borel_space : borel_space R01 := sorry

-- If (X,𝑑) is s Borel space then it is measurable isomorphic to (0,1)

theorem borel_space_iso_Icc_01 (X: Type u₁) [borel_space X] : 
  ∃ (f : X → (set.Icc (0:ℝ) 1)), borel_isomorphism X set_Icc_01_is_borel_space f := sorry