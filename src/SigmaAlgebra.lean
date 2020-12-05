import measure_theory.measurable_space

-- σ-algebra

def A1 : set (set ℕ) := {X, ⊤}
def A1 : set X → Prop := λ a, a ∈ ({⊤ , ∅} : set (set X))
def A2 : set (set ℕ) := set.powerset X
def A2 : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))

-- old school

variables {X : Type} (σ : set (set X))

class sigma_algebra :=
(univ_mem : univ ∈ σ)
(closed_under_comp : ∀ s, s ∈ σ → univ \ s ∈ σ)
(closed_under_countable_union : ∀ f : ℕ → set X, (∀ n, f n ∈ σ) → countable_union f ∈ σ)

-- Eric, measurable_space is sigma-algebra

-- me



#reduce X
#reduce A1
#reduce A2

-- me

def X:Type := fin 3


instance : measurable_space X :=
{ is_measurable' := A1,
  is_measurable_empty := by {rw A1, finish},
  is_measurable_compl := assume a h, by {rw A1 at *, finish},
  is_measurable_Union := assume f hf, by {rw A1 at *, simp, sorry },


def X : Type := fin 3


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



#reduce X
#reduce A1
#reduce A2


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


How do I get the size of an element of A1 or A2? Or even X? When I look at the definition of fin N, it is not clear that N is retained:


I want to be able to define a metric on A1 which is just the size of the finite set. This is not correct but I'm trying to get here:

def SubSet (X: Type) := set X → Prop

def size (X: Type) (F: SubSet X) := sorry

-- docs#measure_theory.measure.count in mathlib

-- the proof that fin n has size n is docs#fintype.card_fin

-- if the set is finite you can use finset.card to get the cardinality

-- you can also use cardinal.mk to get the cardinality of an infinite set but for measures you really just want this to cap out at infinity so the infinite sum on ennreal is the easiest thing to implement

-- the proof that fin n has size n is docs#fintype.card_fin
Alex J. Best: The last part requires a bit more proof, like mario says though, A1 and A2 giving the measurable sets of a measurable space doesn't really require the base type to be fin 3