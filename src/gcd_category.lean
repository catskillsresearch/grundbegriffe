import category_theory.functor
import category_theory.limits.limits
import category_theory.limits.lattice
import data.finset.gcd
import data.nat.gcd
import data.set.finite
import data.nat.fib

open category_theory
open_locale classical
noncomputable theory

instance : has_Sup ℕ := ⟨λ s, if h : s.finite then finset.sup (set.finite.to_finset h) id else (0: ℕ)⟩
instance : complete_lattice ℕ := complete_lattice_of_Sup ℕ  (λ s, sorry)

universe u
variables {α : Type u} [preorder α]

def category_theory.hom_of_dvd {U V : α} (h : (U | V)) : U ⟶  V := ulift.up (plift.up h) -- ERROR
lemma category_theory.dvd_of_hom {U V : α} (h : U ⟶ V) : (U | V) := h.down.down -- ERROR

def nat.fib_as_functor : ℕ ⥤ ℕ :=
{ obj := nat.fib,
  map := λ m n h, hom_of_dvd (nat.fib_dvd_fib (dvd_of_hom h)),
  map_id' := λ _, rfl,
  map_comp' := λ a b c f g, by simp
}

lemma nat.fib_dvd_fib {m n : ℕ }  : (m.fib_as_functor | n.fib_as_functor) :=
begin
  sorry
end

instance : category ℕ := by apply_instance
instance : limits.has_finite_limits ℕ := by apply_instance
