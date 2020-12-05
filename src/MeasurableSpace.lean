import measure_theory.measurable_space

-- Measurable space (S,Σ)

-- Measurable Space: {0,T}, P(T), B((0,1)), B([0,1]), B([0,oo))

structure measurable_space (α : Type*) :=
(is_measurable' : set α → Prop)
(is_measurable_empty : is_measurable' ∅)
(is_measurable_compl : ∀ s, is_measurable' s → is_measurable' sᶜ)
(is_measurable_Union : ∀ f : ℕ → set α, (∀ i, is_measurable' (f i)) → is_measurable' (⋃ i, f i))

import measure_theory.measurable_space



-- Alex

Alex J. Best: The last part requires a bit more proof, like mario says though, A1 and A2 giving the measurable sets of a measurable space doesn't really require the base type to be fin 3

def X:Type := fin 3
def A1 : set X → Prop := λ a, a ∈ ({⊤ , ∅} : set (set X))
def A2 : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))
instance : measurable_space X :=
{ is_measurable' := A1,
  is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp,sorry },
Alex J. Best: The A2 version is easier

instance meas2 : measurable_space X :=
{ is_measurable' := A2,
  is_measurable_empty := by {rw A2, finish},
  is_measurable_compl := assume a h, by {rw A2 at *, finish},
  is_measurable_Union := assume f hf, by {rw A2 at *, simp, }, }

instance meas2 : measurable_space X :=
{ is_measurable' := A2,
  is_measurable_empty := by {rw A2, finish},
  is_measurable_compl := assume a h, by {rw A2 at *, finish},
  is_measurable_Union := assume f hf, by {rw A2 at *, simp, }, }

-- Mario Carneiro: it would be nice to prove these by proving roughly (⊥ : measurable_space X) = A1

-- tactic#finish

-- docs#measurable_space.is_measurable_bot_iff b

-- https://ncatlab.org/nlab/show/measurable+space

-- docs#semigroup.to_has_mul, docs#monoid.to_semigroup, docs#group.to_monoid

def ms_proof (X: Type) (A: set X → Prop) : measurable_space X :=
{ is_measurable' := A,
  is_measurable_empty := by sorry ,
  is_measurable_compl := by sorry ,
  is_measurable_Union := by sorry ,
}

instance M1 : measurable_space X := ms_proof X A1

instance M2 : measurable_space X := ms_proof X A2

--  Yakov

lemma something_about_A1 {X : Type} (sigma : measurable_space X) (h : sigma.is_measurable' = A1) : ... := ...

-- Mario

Mario Carneiro: The proof of the theorems you are talking about in mathlib are done like this:

instance : complete_lattice (measurable_space α) :=
gi_generate_from.lift_complete_lattice

lemma is_measurable_bot_iff {s : set α} : @is_measurable α ⊥ s ↔ (s = ∅ ∨ s = univ) :=
let b : measurable_space α :=
{ is_measurable'      := λ s, s = ∅ ∨ s = univ,
  is_measurable_empty := or.inl rfl,
  is_measurable_compl := by simp [or_imp_distrib] {contextual := tt},
  is_measurable_Union := assume f hf, classical.by_cases
    (assume h : ∃i, f i = univ,
      let ⟨i, hi⟩ := h in
      or.inr $ eq_univ_of_univ_subset $ hi ▸ le_supr f i)
    (assume h : ¬ ∃i, f i = univ,
      or.inl $ eq_empty_of_subset_empty $ Union_subset $ assume i,
        (hf i).elim (by simp {contextual := tt}) (assume hi, false.elim $ h ⟨i, hi⟩)) } in
have b = ⊥, from bot_unique $ assume s hs,
  hs.elim (λ s, s.symm ▸ @is_measurable_empty _ ⊥) (λ s, s.symm ▸ @is_measurable.univ _ ⊥),
this ▸ iff.rfl

@[simp] theorem is_measurable_top {s : set α} : @is_measurable _ ⊤ s := trivial
Mario Carneiro: Here we are starting from a much more powerful fact, that the space of all sigma algebras is a complete lattice, which immediately gives us Sup, Inf, sup, inf, top and bot

Mario Carneiro: and then we prove post hoc that the top and bot so defined are in fact univ and {empty, univ} respectively

Mario Carneiro:
import data.finset.basic
import measure_theory.measurable_space
instance : measurable_space X :=
{ is_measurable' := A1,
  is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp, sorry },

-- Mario

Mario Carneiro: The proof of the theorems you are talking about in mathlib are done like this:

instance : complete_lattice (measurable_space α) :=
gi_generate_from.lift_complete_lattice

lemma is_measurable_bot_iff {s : set α} : @is_measurable α ⊥ s ↔ (s = ∅ ∨ s = univ) :=
let b : measurable_space α :=
{ is_measurable'      := λ s, s = ∅ ∨ s = univ,
  is_measurable_empty := or.inl rfl,
  is_measurable_compl := by simp [or_imp_distrib] {contextual := tt},
  is_measurable_Union := assume f hf, classical.by_cases
    (assume h : ∃i, f i = univ,
      let ⟨i, hi⟩ := h in
      or.inr $ eq_univ_of_univ_subset $ hi ▸ le_supr f i)
    (assume h : ¬ ∃i, f i = univ,
      or.inl $ eq_empty_of_subset_empty $ Union_subset $ assume i,
        (hf i).elim (by simp {contextual := tt}) (assume hi, false.elim $ h ⟨i, hi⟩)) } in
have b = ⊥, from bot_unique $ assume s hs,
  hs.elim (λ s, s.symm ▸ @is_measurable_empty _ ⊥) (λ s, s.symm ▸ @is_measurable.univ _ ⊥),
this ▸ iff.rfl

@[simp] theorem is_measurable_top {s : set α} : @is_measurable _ ⊤ s := trivial
Mario Carneiro: Here we are starting from a much more powerful fact, that the space of all sigma algebras is a complete lattice, which immediately gives us Sup, Inf, sup, inf, top and bot

Mario Carneiro: and then we prove post hoc that the top and bot so defined are in fact univ and {empty, univ} respectively


Mario Carneiro:
import data.finset.basic
import measure_theory.measurable_space

def X : Type := fin 3
def A1 : set X → Prop := λ a, a ∈ ({⊤ , ∅} : set (set X))
def A2 : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))

def measurable_space.copy {α} (c : measurable_space α)
  (P : set α → Prop) (eq_P : ∀ s, P s ↔ @is_measurable _ c s) :
  measurable_space α :=
begin
  replace eq_P : P = c.is_measurable' := by ext; apply eq_P,
  refine { is_measurable' := P, .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

theorem measurable_space.copy_eq {α} (c P eq_P) :
  @measurable_space.copy α c P eq_P = c :=
measurable_space.ext eq_P

def foo1 : measurable_space X :=
measurable_space.copy ⊥ A1 $
by simp [measurable_space.is_measurable_bot_iff, A1, eq_comm, or.comm]

def foo2 : measurable_space X :=
measurable_space.copy ⊤ A2 $ by simp [A2]

theorem foo1_eq : foo1 = ⊥ := measurable_space.copy_eq _ _ _
theorem foo2_eq : foo2 = ⊤ := measurable_space.copy_eq _ _ _

def M1 : measurable_space X :=
measurable_space.copy ⊥ A1 $
by simp [measurable_space.is_measurable_bot_iff, A1, eq_comm, or.comm]

def M2 : measurable_space X :=
measurable_space.copy ⊤ A2 $ by simp [A2]

theorem M1_eq : M1 = ⊥ := measurable_space.copy_eq _ _ _
theorem M2_eq : M2 = ⊤ := measurable_space.copy_eq _ _ _

instance : fintype X := fin.fintype _
noncomputable instance foo (s : set X) : fintype s := by classical; apply_instance

import measure_theory.measurable_space

def measurable_space.copy {α} (c : measurable_space α)
  (P : set α → Prop) (eq_P : ∀ s, P s ↔ @is_measurable _ c s) :
  measurable_space α :=
begin
  replace eq_P : P = c.is_measurable' := by ext; apply eq_P,
  refine { is_measurable' := P, .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

theorem measurable_space.copy_eq {α} (c P eq_P) :
  @measurable_space.copy α c P eq_P = c :=
measurable_space.ext eq_P

def foo1 : measurable_space X :=
measurable_space.copy ⊥ A1 $
by simp [measurable_space.is_measurable_bot_iff, A1, eq_comm, or.comm]

def foo2 : measurable_space X :=
measurable_space.copy ⊤ A2 $ by simp [A2]

theorem foo1_eq : foo1 = ⊥ := measurable_space.copy_eq _ _ _
theorem foo2_eq : foo2 = ⊤ := measurable_space.copy_eq _ _ _


-- me

import data.finset.basic
import measure_theory.measurable_space
import measure_theory.measure_space

open measure_theory

def measurable_space.copy {α} (c : measurable_space α)
  (P : set α → Prop) (eq_P : ∀ s, P s ↔ @is_measurable _ c s) :
  measurable_space α :=
begin
  replace eq_P : P = c.is_measurable' := by ext; apply eq_P,
  refine { is_measurable' := P, .. },
  all_goals { abstract { subst_vars, casesI c, assumption } }
end

theorem measurable_space.copy_eq {α} (c P eq_P) :
  @measurable_space.copy α c P eq_P = c :=
measurable_space.ext eq_P

def M1 : measurable_space X :=
measurable_space.copy ⊥ A1 $
by { simp [measurable_space.is_measurable_bot_iff,
        A1,
        eq_comm,
        or.comm],
     sorry }

theorem M1_eq : M1 = ⊥ := measurable_space.copy_eq _ _ _

instance : measurable_space X :=
{ is_measurable' := A1,
  is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp, sorry },

#check measurable_space S

import measure_theory.measurable_space

#check measurable_space A1
#check measurable_space A2

def M1 : measurable_space X :=
measurable_space.copy ⊥ A1 $
by simp [measurable_space.is_measurable_bot_iff, A1, eq_comm, or.comm]

def M2 : measurable_space X :=
measurable_space.copy ⊤ A2 $ by simp [A2]

theorem M1_eq : M1 = ⊥ := measurable_space.copy_eq _ _ _
theorem M2_eq : M2 = ⊤ := measurable_space.copy_eq _ _ _


def A1 : set X → Prop := λ a, a ∈ ({⊤ , ∅} : set (set X))
def A2 : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))
How do I get the size of an element of A1 or A2? Or even X? When I look at the definition of fin N, it is not clear that N is retained:


I want to be able to define a metric on A1 which is just the size of the finite set. This is not correct but I'm trying to get here:

def SubSet (X: Type) := set X → Prop

def size (X: Type) (F: SubSet X) := sorry

-- docs#measure_theory.measure.count in mathlib

-- the proof that fin n has size n is docs#fintype.card_fin

-- if the set is finite you can use finset.card to get the cardinality

-- you can also use cardinal.mk to get the cardinality of an infinite set but for measures you really just want this to cap out at infinity so the infinite sum on ennreal is the easiest thing to implement

-- the proof that fin n has size n is docs#fintype.card_fin

def finite_set_measure_of(X: Type): SubSet X → ennreal := λ F, size X F

-- you have to prove that finite cardinalities are countably additive
import data.finset.basic

def X : Type := fin 3
def X : set ℕ := ({1, 2, 3} : finset ℕ)