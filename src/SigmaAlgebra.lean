import measure_theory.measurable_space

def X : Type := fin 3

def A : set X → Prop := λ a, a ∈ (𝒫 ⊤ : set (set X))

structure σ_algebra (X : Type*) (A : set X → Prop) :=
(carrier_set : Type*)
(algebra : set X → Prop)
(is_measurable_empty : A ∅)
(is_measurable_compl : ∀ s, A s → A sᶜ)
(is_measurable_Union : ∀ f : ℕ → set X, (∀ i, A (f i)) → A (⋃ i, f i))

attribute [class] σ_algebra

instance XA: σ_algebra X A :=
{ carrier_set := X,
  algebra := A,
  is_measurable_empty := by {rw A, finish},
  is_measurable_compl := assume a h, by {rw A at *, finish},
  is_measurable_Union := assume f hf, by {rw A at *, simp },
}

#check XA -- XA : σ_algebra X A

def to_measurable_space (X : Type) (A : set X → Prop) (XA : σ_algebra X A) : (measurable_space X) :=
{ is_measurable' := A,
  is_measurable_empty := XA.is_measurable_empty,
  is_measurable_compl := XA.is_measurable_compl,
  is_measurable_Union := XA.is_measurable_Union,
}

instance M : measurable_space X := to_measurable_space X A XA

#check M -- M : measurable_space X

/- def to_measurable_space1  (XA : σ_algebra X A) : (measurable_space X) :=
{ is_measurable' := XA.algebra,
  is_measurable_empty := XA.is_measurable_empty,
  is_measurable_compl := XA.is_measurable_compl,
  is_measurable_Union := XA.is_measurable_Union,
}

instance M1 : measurable_space X := to_measurable_space1 XA

#check M1 -- M : measurable_space X -/

/- def measurable_space.copy {α} (c : measurable_space α)
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

set_option trace.simp_lemmas true

#check A
#check XA.algebra

def foo2 : measurable_space X := measurable_space.copy ⊤ XA.algebra $ by simp [XA.algebra]

#check foo2 -/