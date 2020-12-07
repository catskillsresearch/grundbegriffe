import measure_theory.measurable_space

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