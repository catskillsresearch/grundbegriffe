-- Mathematical definitions underlying numerical solution of stochastic differential equations

import algebra.group.defs
import algebra.group_with_zero.defs
import data.finset.basic
import data.nat.basic
import data.real.basic
import data.real.ennreal
import data.real.ereal
import data.set.intervals.basic
import init.meta.tactic
import measure_theory.borel_space
import measure_theory.lebesgue_measure
import measure_theory.measurable_space
import measure_theory.measure_space
import order.conditionally_complete_lattice
import order.complete_lattice
import tactic
import topology.metric_space.basic

set_option trace.class_instances true

open measure_theory
open quot

noncomputable theory

-- ℕ

instance X_add_semigroup : add_semigroup ℕ := nat.add_semigroup
#check (by apply_instance : ordered_add_comm_monoid ℕ)
#check (by apply_instance : canonically_ordered_add_monoid ℕ)
#check (by apply_instance : canonically_ordered_comm_semiring ℕ)
#check (by apply_instance : monoid_with_zero ℕ)
#check nat.distrib
#check nat.monoid -- nat.monoid : monoid ℕ
#check nat.mul_zero_class -- unknown identifier 'nat.mul_zero_class'--

#check (by apply_instance: complete_lattice (set ℕ ))

#check enat.complete_linear_order import data.nat.basic
#check (by apply_instance: has_bot ℕ )

#check nat.has_Inf
#check nat.has_Sup

#check linear_order ℕ import data.nat.basic
#check nat.monoid -- nat.monoid : monoid ℕ

#check (by apply_instance : mul_zero_class ℕ)
#check (by apply_instance: partial_order ℕ)
#check (by apply_instance: preorder ℕ)

lemma nat_le_trans (a b c : ℕ ) : a ≤ b → b ≤ c → a ≤ c := nat.le_trans

instance : preorder ℕ := {
  le := (≤),
  le_refl := nat.le_refl,
  le_trans := nat_le_trans,
}

-- Finite subsets of ℕ

namespace finite_subsets_of_ℕ_with_fin

def X := fin 3
instance X_nontrivial : nontrivial X := fin.nontrivial
instance X_has_add : has_add (fin 3):= fin.has_add

@[reducible]
def A := set (fin 3)

def plus (x y : A) := x ∪ y

end finite_subsets_of_ℕ_with_fin

namespace finite_subsets_of_ℕ_with_finset

def S1A : finset ℕ := {1, 2, 3}
def S1B : set ℕ := ({1, 2, 3} : finset ℕ)
def S2 : set ℕ := {n : ℕ | 0 < n ∧ n ≤ 3}

example : 1 ∈ S2 := 
  set.left_mem_Icc.mpr (show 1 ≤ 3, from dec_trivial)

def S3 : set (fin 3) := ⊤ 

def S3A : set ℕ := S3

instance : has_add ( finset ℕ  ) := ⟨ λ x y, x ∪ y ⟩

def X : set ℕ := ({1, 2, 3} : finset ℕ)

#check (by apply_instance : ∀ n, has_bot (set (fin n)))
#check (by apply_instance : ∀ n, has_top (set (fin n)))
#check (by apply_instance : ∀ n, order_bot (set (fin n)))
#check (by apply_instance : ∀ n, order_top (set (fin n)))
#check (by apply_instance : ∀ n, has_sup(set (fin n)))
#check (by apply_instance : ∀ n, has_inf(set (fin n)))
#check (by apply_instance : ∀ n, semilattice_sup(set (fin n)))
#check (by apply_instance : ∀ n, semilattice_inf(set (fin n)))
#check (by apply_instance : ∀ n, lattice(set (fin n)))
#check (by apply_instance : ∀ n, bounded_lattice(set (fin n)))

def X : set ℕ := ({1, 2, 3} : finset ℕ)
def mul (x y : set X) : set X := (x ∩ y : set X)
instance X_has_mul : has_mul (set X) := ⟨ mul ⟩
theorem X_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance X_semigroup : semigroup (set X) := ⟨ mul, X_mul_assoc ⟩

end finite_subsets_of_ℕ_with_finset

-- ℚ

-- ℝ

def μ := measure_theory.real.measure_space.volume
#check borel_space ℝ 

-- Borel σ-algebra B(ℝ)
-- Cauchy-complete metric space
-- Clopen set
-- Closed set X on a metric space
-- Conditional expectation
-- Continuous random variable density function
-- Continuous random variable
-- Diameter diam(X) for X ⊆ M of metric space (M,d)
-- Discrete random variable
-- Distribution function F_X: ℝ→ [0,1]
-- F_V(E) = P({x \in X: V(x) ≤ e}) be the *distribution function*

-- Clearly F_V(E) is well defined for any metric space (Y,d) provided with a relation a \leq b for all a,b \in Y.

-- All metric spaces can be totally ordered.
-- Not all metric spaces have a total order which is "compatible with the ring structure".  (So: not sensible or useful in that specific sense.)  For example, the complex numbers \mathbb C.
-- 
-- So in the strict sense that all metric spaces can be totally ordered, the distribution function always exists, but it may be "uninteresting".
-- 
-- So to be "obviously useful", it is only necessary to stipulate that the metric space (Y,d) is an "obviously useful" ordered metric space.  Here we have range of possible more or less useful orderings:
-- 
-- Y is a [partially ordered set][2]
-- Y has a partial order compatible with the ring structure
-- Y is a [totally ordered set][3]
-- Y is a [Complete metric space][4]

--  [1]: https://math.stackexchange.com/questions/1429373/why-is-there-no-order-in-metric-spaces
--  [2]: https://en.wikipedia.org/wiki/Partially_ordered_set
--  [3]: https://en.wikipedia.org/wiki/Total_order
--  [4]: https://en.wikipedia.org/wiki/Complete_metric_space


-- Distribution μ_X : Σ → [0,1]
-- μ_V(E) = P(V^{-1}(E)) be the *distribution*-- Distribution space (S,Σ ,μ_X )
-- Event space A
-- Exponential continuous random variable
-- Family of sets A

-- Finite Borel measure μ: B(M) → [0,∞) of metric space (M,d)
-- Finite measure p: A→[0,∞)

instance fin_n_partial_order (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

lemma fin_n_partial_order1 (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

def fin_n_partial_order2 (n: ℕ) : partial_order (fin n) := 
  subtype.partial_order (λ (i : ℕ), i < n)

example : (∀ n : ℕ , partial_order (fin n)) :=
begin
  intro h,
  exact subtype.partial_order (λ (i : ℕ), i < _),
end

#check (by apply_instance : ∀ n, partial_order (fin n))

instance X_is_nontrivial : nontrivial (fin 3) := fin.nontrivial
#check X_is_nontrivial --X_is_nontrivial : nontrivial X

instance X_has_add : has_add (fin 3):= fin.has_add
#check X_has_add -- X_has_add : has_add X

def I : Type* := set.Icc (0 : ℝ) 1
instance foo0 : topological_space I := by {unfold I, apply_instance}
instance foo1 : measurable_space I := borel I
instance foo2 : borel_space I := ⟨rfl⟩
#check foo2

def B01 : borel_space I := by apply_instance -- now it works.
#check B01


#check μ -- μ : measure_theory.measure ℝ

#check probability_measure μ


instance inhabitant : fintype (fin 1) := fin.fintype 1

def A :=  λ a, a ∈ (𝒫 ⊤ : set (set (fin 1)))

def M : measurable_space (fin 1) := { is_measurable_empty := by {rw A, finish},
  is_measurable' := A,
  is_measurable_compl := assume a h, by {rw A at *, finish},
  is_measurable_Union := assume f hf, by {rw A at *, simp },
}

noncomputable abbreviation qlbrdl (s: set (fin 1)) (z: @is_measurable (fin 1) M s) : ennreal := 
  finset.card s.to_finset

noncomputable def μ : @measure_theory.measure (fin 1) M :=
@measure_theory.measure.of_measurable _ M
  (qlbrdl)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)
-- V^{-1}(E) = {x \in X: V(x) \in E} be the generalized inverse of V
-- Σ(A) the sigma algebra generated by a family of sets A
-- InhabitedSet
-- SampleSpace
-- Algebra
-- σAlgebra
-- EventSpace
-- FamilyOfSets
-- GeneratedSigmaAlgebra
-- SigmaAdditiveFunction
-- TopologicalSpace
-- Homeomorphism
-- SeparableTopologicalSpace
-- Metric
-- MetricSpace
-- OpenSetOnAMetricSpace
-- OpenSetsOfAFamily
-- ClosedSetOnAMetricSpace
-- ClopenSet
-- Reals
-- RealIntervals

namespace real_interval_examples

#check (by apply_instance : measurable_space (set.Ioo (0:ℝ) 1))
#check (by apply_instance : measurable_space (set.Icc (0:ℝ) 1))
#check (by apply_instance : measurable_space (set.Ici (0:ℝ)))

end real_interval_examples

-- RealMetric
-- BorelSigmaAlgebraOfMetricSpace
-- BorelSigmaAlgebraOfR
-- BorelSigmaAlgebraOfRealInterval
-- BorelSetOfMetricSpace
-- FiniteBorelMeasure
-- BorelProbabilityMeasure
-- DiametricOfAMetricSpace
-- CauchyCompleteMetricSpace
-- Measure
-- MeasurableSpace
-- MeasurableFunction
-- Pullback
-- PushForwardMeasure
-- MeasureSpace
-- FiniteMeasure
-- LebesgueSigmaAlgebra
-- LebesgueOuterMeasure
-- LebesgueMeasure
-- PolishMeasurableSpace
-- ProbabilityMeasure
-- ProbabilitySpace
-- RandomVariable
-- GeneralizedInverse
-- Distribution
-- DistributionSpace
-- DistributionFunction
-- QuantileFunction
-- RealDistributionSpace
-- SteinhausSpace
-- DiscreteRandomVariable
-- ContinuousRandomVariable
-- ContinuousRandomVariableDensityFunction
-- UniformContinuousRandomVariable
-- ExponentialContinuousRandomVariable
-- NormalContinuousRandomVariable
-- IIDRandomSequenceFromRealNumber
-- StochasticKernel
-- AlmostSurely
-- Version
-- TransitionKernel
-- TransitionProbabilityKernel
-- RegularVersion
-- ConditionalExpectation
-- StochasticProcess
-- Homeomorphism
-- Construction of i.i.d random sequences from individual numbers in ℝ

-- A set with 3 elements

-- Lebesgue measure λ : L(ℝ) → [0,∞)
-- Lebesgue outer measure λ⋆ : L(ℝ) → [0,∞)
-- Lebesgue σ-algebra L(ℝ)
-- Measurable function f

-- Measurable space (S,Σ), S a set, Σ a σ-algebra on S

-- Examples: {0,T}, P(T), B((0,1)), B([0,1]), B([0,oo))

-- Measure μ: A → [0,∞)

-- Example 0

instance inhabitant : fintype (fin 1) := fin.fintype 1

def A :=  λ a, a ∈ (𝒫 ⊤ : set (set (fin 1)))

def M : measurable_space (fin 1) := { is_measurable_empty := by {rw A, finish},
  is_measurable' := A,
  is_measurable_compl := assume a h, by {rw A at *, finish},
  is_measurable_Union := assume f hf, by {rw A at *, simp },
}

noncomputable abbreviation qlbrdl (s: set (fin 1)) (z: @is_measurable (fin 1) M s) : ennreal := 
  finset.card s.to_finset

noncomputable def μ : @measure_theory.measure (fin 1) M :=
@measure_theory.measure.of_measurable _ M
  (qlbrdl)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

-- Example 1

instance witness : fintype X := fin.fintype 3

noncomputable def μ_M1 : @measure_theory.measure X M1 :=
@measure_theory.measure.of_measurable _ M1
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

-- Example 2

noncomputable def μ_M2 : @measure_theory.measure X M2 :=
@measure_theory.measure.of_measurable _ M2
  (λ s _, finset.card s.to_finset)
  (by simp)
  (λ x h a, begin simp, sorry end)

-- Measure space (S,Σ,μ)

-- Example 1 : 𝒫 ⊤

noncomputable def M1_MS : measure_space X := {
  to_measurable_space := M1,
  volume := μ_M1 }

noncomputable def M2_MS : measure_space X := {
  to_measurable_space := M2,
  volume := μ_M2 }

-- Example 3: B(ℝ)

#check measure_theory.measure_space.volume
#check measure_theory.real.measure_space
#check (volume : measure ℝ) -- Lebesgue measure on ℝ 

-- Example 4: B([0,1])


-- Example 1

noncomputable def d_L1 := λ (x y : ℝ), abs (x - y)
noncomputable def R_has_dist_L1 : has_dist ℝ := ⟨ d_L1 ⟩ 

-- Example 2

noncomputable def d_L2 := λ (x y : ℝ), real.sqrt ((x - y)^2)
noncomputable def R_has_dist_l2 : has_dist ℝ := ⟨ d_L2 ⟩ 

-- Example 3

abbreviation RealPoint : Type := ℝ × ℝ -- real points

noncomputable def d_taxicab := λ (x y : RealPoint), (abs (x.1 - y.1)) + (abs (x.2 - y.2))
noncomputable def RealPoint_has_dist_taxicab : has_dist RealPoint := ⟨ d_taxicab ⟩ 

-- Example 4

noncomputable def d_euclid  := λ (x y : RealPoint), real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2)
noncomputable def RealPoint_has_dist_euclid : has_dist RealPoint := ⟨ d_taxicab ⟩ 

-- Metric space

-- Example 1

noncomputable def MES_L1 : metric_space ℝ :=
{ dist := d_L1,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L1 -- MES_L1 : metric_space ℝ

-- Example 2

noncomputable def MES_L2 : metric_space ℝ :=
{ dist := d_L2,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L2 -- MES_L2 : metric_space ℝ

-- Example 3

noncomputable def MES_taxicab : metric_space RealPoint :=
{ dist := d_taxicab,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_taxicab -- MES_taxicab : metric_space RealPoint

-- Example 4

noncomputable def MES_euclid: metric_space RealPoint :=
{ dist := d_euclid,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_euclid -- MES_taxicab : metric_space RealPoint
#check nat.add_comm_semigroup 
#check nat.add_comm_monoid


namespace version_1


end version_1

namespace version_2

-- Normal continuous random variable
-- Open set U on a metric space
-- Open sets O(F) of a family F
-- Polish measurable space
-- Probability measure p: Σ → [0,1]

instance inhabitant : fintype (fin 1) := fin.fintype 1

def A :=  λ a, a ∈ (𝒫 ⊤ : set (set (fin 1)))

def M : measurable_space (fin 1) := { is_measurable_empty := by {rw A, finish},
  is_measurable' := A,
  is_measurable_compl := assume a h, by {rw A at *, finish},
  is_measurable_Union := assume f hf, by {rw A at *, simp },
}

noncomputable abbreviation qlbrdl (s: set (fin 1)) (z: @is_measurable (fin 1) M s) : ennreal := 
  finset.card s.to_finset

noncomputable def μ : @measure_theory.measure (fin 1) M :=
@measure_theory.measure.of_measurable _ M
  (qlbrdl)
  (by simp)
  (λ x h a, begin
    simp,
    sorry
  end)

def P : (@measure_theory.probability_measure (fin 1) M μ) := 
{ measure_univ := sorry }

#check P
#check M
#check real.measurable_space
#check real.borel_space
instance B01 : borel_space ℝ := ⟨rfl⟩
#check B01

-- define
-- instance subtype.measure_space
-- using coercion and

#check measure_theory.measure.comap

instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure:  probability_measure volume)

-- Example 1: Steinhaus space

abbreviation I01 := (set.Icc (0 : ℝ) 1)

instance P_I01 : probability_measure (volume : measure I01) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume I01 = 1, {simpa},
    rw [real.volume_Icc], simp
  end }

instance Steinhaus : probability_space I01 := 
{ is_probability_measure := P_I01 }

#check Steinhaus -- Steinhaus : probability_space ↥I01

-- Example 2: Finite space X over {0,1,2} and σ-algebra 𝒫 X

def X : Type := fin 3
def A : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))

instance X_is_nontrivial : nontrivial X := fin.nontrivial

#check X_is_nontrivial
-- Pullback f⁻¹: Σ → A
-- Push-forward measure f(μ): T → [0,∞)

namespace finite_add_monoid_example

def X : set ℕ := ({1, 2, 3} : finset ℕ)

def plus (x y : set X) : set X := (x ∪ y : set X)
instance : has_add (set X) := ⟨ plus ⟩

instance : has_zero (set X) := ⟨ ∅ ⟩ 

lemma zero_add (a : set X) : 0 + a = a := bot_sup_eq

lemma add_zero (a : set X) : a + 0 = a := sup_bot_eq

lemma add_assoc ( a b c : set X) : a + b + c = a + (b + c) := sup_assoc

instance : add_monoid (set X) :=
{
  add := (+),
  zero := ∅,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
}

end finite_add_monoid_example

def X := fin 3
def plus (x y : set X) : set X := (x ∪ y : set X)
instance PX_has_add : has_add (set X):= ⟨ plus ⟩ 
#check PX_has_add -- X_has_add : has_add X

def X := fin 3
def PX_mul (x y : set X) : set X := (x ∩ y : set X)
instance PX_has_mul : has_mul (set X) := ⟨ PX_mul ⟩ 


namespace finite_monoid_example

def X : set ℕ := ({1, 2, 3} : finset ℕ)
def mul (x y : set X) : set X := (x ∩ y : set X)
instance : has_mul (set X) := ⟨ mul ⟩
lemma mul_assoc (x y z : set X) : (x * y) * z = x * (y * z) := inf_assoc
instance : has_one (set X) := ⟨ set.univ ⟩ 
lemma one_mul (a : set X) : 1 * a = a := top_inf_eq
lemma mul_one (a : set X): a * 1 = a := inf_top_eq

instance : monoid (set X) :=
{
  one := 1,
  mul := (*),
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one
}

end finite_monoid_example

namespace finite_powerset_mul_zero_example

def X := fin 3
def mul (x y : set X) : set X := (x ∩ y : set X)
instance has_mul : has_mul (set X) := ⟨ mul ⟩ 
instance has_zero : has_zero (set X) := ⟨ ∅ ⟩ 
lemma zero_mul (a : set X): 0 * a = 0 := bot_inf_eq
lemma mul_zero (a : set X): a * 0 = 0 := inf_bot_eq

instance : mul_zero_class (set X) := {
  mul := has_mul.mul,
  zero := ∅,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
} 

end finite_powerset_mul_zero_example
def X := fin 3
instance : nontrivial X := fin.nontrivial
instance : nontrivial (set X) := nontrivial_of_ne _ _ set.empty_ne_univ.symm

-- def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X := fin 3
def PX_mul (x y : set X) : set X := (x ∩ y : set X)
instance PX_has_mul : has_mul (set X) := ⟨ PX_mul ⟩ 
theorem PX_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance PX_semigroup : semigroup (set X) := ⟨ PX_mul, PX_mul_assoc ⟩
-- Quantile function T-:[0,1]→ ereal of function T:ℝ→ [0,1] maybe a/k/a inverse distribution function F^-X of distribution function F_X
-- Random variable (Ω,A,P)→(S,Σ) from probability space to measure space
-- V: (X, Σ) \→  (Y,d) be a Y-valued random variable

variables (X Y : Type) [measurable_space X] [measurable_space Y] [metric_space Y] [borel_space Y] (x : X → Y)
#check measurable x -- x is a Y-valued RV on X

Let (𝑋,Σ) be a measure space.

Let (𝑌,𝑑) be a metric space.

Let 𝑥 be a map from 𝑋 to 𝑌 such that (inv x)(𝐵)∈Σ for any Borel set 𝐵 in 𝑌 .

We say that 𝑥:(𝑋,Σ)→(𝑌,𝑑) is a 𝑌 -valued random function and 𝑥 is a Σ -measurable function.

We say that 𝑥 is a 𝑌 -valued random variable iff

(inv x)(𝑂)∈Σ for any open set 𝑂
(inv x)(𝑆)∈Σ for any closet set 𝑆
If 𝑌=ℜ , then {𝑤∈𝑋:𝑥(𝑤)≤𝛼}∈Σ for any 𝛼∈ℜ ."

variables (X Y : Type) [measurable_space X]
  [measurable_space Y] [metric_space Y] [borel_space Y] (x : X → Y)

#check measurable x -- x is a Y-valued RV on X


#check nnreal.densely_ordered
def with_top (α : Type*) := option α-- Real distribution space (ℝ, B(ℝ), μ_x, F_X) from distribution μ_x on real-valued random variable on (Ω,A,P)
-- Real closed/open intervals [a,b], (a,b), [a,b), (a,b], (0,1), [0,1], [0,∞).

def O01 : set ℝ := set.Ioo 0 1 -- (0,1)
def C01 : set ℝ := set.Icc 0 1 -- [0,1]
def C0oo : set ereal := set.Ici 0 -- [0,∞)
-- Real metric dR: ℝ × ℝ → [0,∞)
-- ℝ
-- Regular version
-- Sample space: inhabited set
-- Separable topological space
-- σ-additive function

structure is_σ_algebra (X : Type*) (A : set X → Prop) :=
(is_measurable_empty : A ∅)
(is_measurable_compl : ∀ s, A s → A sᶜ)
(is_measurable_Union : ∀ f : ℕ → set X, (∀ i, A (f i)) → A (⋃ i, f i))

def is_σ_algebra.carrier_set {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A):= X
def is_σ_algebra.algebra {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A) := A

def to_measurable_space  {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A) : (measurable_space X) :=
{ is_measurable' := XA.algebra,
  is_measurable_empty := XA.is_measurable_empty,
  is_measurable_compl := XA.is_measurable_compl,
  is_measurable_Union := XA.is_measurable_Union,
}

-- Example 1

def X : Type := fin 3

def A1 : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))

def XA1: is_σ_algebra X A1 :=
{ is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp },
}

#check XA1 -- XA : is_σ_algebra X A
#check is_σ_algebra.carrier_set XA1 -- XA1.carrier_set : Type

def M1 : measurable_space X := to_measurable_space XA1

#check M1

-- Example 2

def A2 : set X → Prop := λ a, a ∈ ({⊤ , ∅} : set (set X))

def XA2: is_σ_algebra X A2 :=
{ is_measurable_empty := by {rw A2, finish},
  is_measurable_compl := assume a h, by {rw A2 at *, finish},
  is_measurable_Union := assume f hf, by {rw A2 at *, simp, sorry },
}

def M2 : measurable_space X := to_measurable_space XA2

instance {α} {p : α → Prop} [m : measure_space α] : measure_space (subtype p) :=
{ volume := measure.comap (coe : _ → α) volume }

theorem subtype.volume_apply {α} {p : α → Prop} [measure_space α]
  (hp : is_measurable {x | p x}) {s : set (subtype p)} (hs : is_measurable s) :
  volume s = volume ((coe : _ → α) '' s) :=
measure.comap_apply _ subtype.coe_injective (λ _, is_measurable.subtype_image hp) _ hs

class probability_space (α : Type*) extends measure_space α :=
(is_probability_measure:  probability_measure volume)

class random_variable (α β : Type*) := 
(experiment : α → β )
(is_probability_space : probability_space α)
(is_metric_space : metric_space β)
(generalized_inverse : set β → set α := λ E : set β, {x : α // (experiment x) ∈ E})
(distribution : λ E : set β, is_probability_space.volume (c.generalized_inverse E))
(distribution_function : λ E : set β )

instance Steinhaus_measure : probability_measure (volume : measure (set.Icc (0 : ℝ) 1)) :=
{ measure_univ := begin
    refine (subtype.volume_apply is_measurable_Icc is_measurable.univ).trans _,
    suffices : volume (set.Icc (0 : ℝ) 1) = 1, {simpa},
    rw [real.volume_Icc], simp
  end 
}

instance Steinhaus_space : probability_space (set.Icc (0 : ℝ) 1) := 
{ is_probability_measure := Steinhaus_measure }-- Stochastic kernel
-- Stochastic process
-- Topological space
-- Transition kernel
-- Transition probability kernel
-- Uniform continuous random variable
-- Version

def X := fin 3
def plus (x y : set X) : set X := (x ∪ y : set X)
instance X_has_add : has_add (set X) := ⟨ plus ⟩
theorem X_add_assoc (x y z : set X) :  (x + y) + z = x + (y + z) := sup_assoc
instance X_add_semigroup : add_semigroup (set X) := ⟨ plus, X_add_assoc ⟩
def X : set ℕ := ({1, 2, 3} : finset ℕ)
def plus (x y : set X) : set X := (x ∪ y : set X)
instance X_has_add : has_add (set X) := ⟨ plus ⟩
theorem X_add_assoc (x y z : set X) :  (x + y) + z = x + (y + z) := sup_assoc
instance X_add_semigroup : add_semigroup (set X) := ⟨ plus, X_add_assoc ⟩ 


lemma X_add_semigroup : add_semigroup ℕ := nat.add_semigroup
#check X_add_semigroup -- X_has_add_semigroup : add_semigroup ℕ

def X := fin 3
instance X_has_add : has_add X := fin.has_add
#check X_has_add -- X_has_add : has_add X

def X := fin 3
instance X_has_mul : has_mul X := fin.has_mul
#check X_has_mul -- X_has_mul : has_mul X

namespace has_one_finite_fin_3
def X := fin 3
instance : nontrivial X := fin.nontrivial
instance : has_one X := fin.has_one
end has_one_finite_fin_3

namespace has_one_finite_finset_123
def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X_one : X := ⟨1,set.mem_insert 1 (λ (b : ℕ), b = 2 ∨ list.mem b [3])⟩
instance : has_one X := { one := X_one }
end has_one_finite_finset_123

namespace finite_zero_example_fin_3
def X := fin 3
instance : has_zero X := fin.has_zero
end finite_zero_example_fin_3

namespace finite_zero_example_finset_012
def X : set ℕ := ({0,1,2} : finset ℕ)
def X_zero : X := ⟨0,set.mem_insert 0 (λ (b : ℕ), b = 1 ∨ list.mem b [2])⟩
instance : has_zero X := { zero := X_zero }
end finite_zero_example_finset_012

namespace finite_zero_example_set_fin3
def X := fin 3
instance : has_zero X := fin.has_zero
instance : has_zero (set X) := ⟨ ∅ ⟩ 
end finite_zero_example_set_fin3
semigroup

def X := fin 3
def mul (x y : set X) : set X := (x ∩ y : set X)
instance X_has_mul : has_mul (set X) := ⟨ mul ⟩
instance X_has_one : has_one set X := fin.has_one
theorem X_mul_assoc (x y z : set X) :  (x * y) * z = x * (y * z) := inf_assoc
instance X_semigroup : semigroup (set X) := ⟨ mul, X_mul_assoc ⟩

#check X_has_one.one

instance X_monoid : monoid (set X) := 
{
    mul := X_has_mul.mul,
    one := X_has_one.one,
    mul_assoc := sorry,
    one_mul := sorry,
    mul_one := sorry,
}

namespace finite_mul_zero_example_fin_3

def X := fin 3
instance : has_mul X := fin.has_mul
instance : has_zero X := fin.has_zero

lemma zero_mul (a : X): 0 * a = 0 := 
begin
  sorry
end

lemma mul_zero (a : X): a * 0 = 0 := 
begin
  sorry
end

instance : mul_zero_class X := {
 mul := (*),
 zero := 0,
 zero_mul := zero_mul,
 mul_zero := mul_zero }

end finite_mul_zero_example_fin_3
-- nontrivial {0,1,2}

def X := fin 3
instance X_nontrivial : nontrivial X := fin.nontrivial
#check X_nontrivial --X_nontrivial : nontrivial X

instance : nontrivial (set X) :=
begin
  unfold X, 
  apply_instance
end
/- def X := fin 3

instance : nontrivial X := fin.nontrivial

instance PX_has_one : has_one (set X) :=
{ one := set.univ } -/

def X : set ℕ := ({1, 2, 3} : finset ℕ)
def X_one : X := ⟨1,set.mem_insert 1 (λ (b : ℕ), b = 2 ∨ list.mem b [3])⟩
instance X_has_one : has_one X := { one := X_one }

def X_one' : set ℕ := ({1} : finset ℕ)

#check X_one -- X_one : ↥X
#reduce X_one -- ⟨1, _⟩

#check X_one' -- X_one' : set ℕ
#reduce X_one' -- λ (x : ℕ), x = 1 ∨ false


