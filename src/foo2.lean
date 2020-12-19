import data.nat.fib
import category_theory.functor
import category_theory.limits.limits
import category_theory.limits.lattice
import data.finset.gcd
import data.set.finite
import tactic
open category_theory

def mynat : Type := nat
def to_nat : mynat → nat := id
instance : has_dvd mynat :=
{dvd := λ a b, to_nat a ∣ b}

instance : semilattice_sup_bot mynat :=
{ le := (∣),
le_refl := λ a, dvd_refl a,
le_trans := λ a b c h g, dvd_trans h g,
bot := (1 : ℕ),
sup := λ a b , nat.lcm a b,
le_antisymm := λ a b, nat.dvd_antisymm,
le_sup_left := nat.dvd_lcm_left,
le_sup_right := nat.dvd_lcm_right,
bot_le := λ (a:ℕ), ⟨a, (one_mul a).symm⟩,
sup_le := λ a b c, nat.lcm_dvd,
 }

open_locale classical
noncomputable theory
instance : has_Sup mynat := ⟨
  λ s, if h : s.finite 
       then finset.sup (set.finite.to_finset h) id 
       else (0: ℕ)⟩

instance : complete_lattice mynat := 
complete_lattice_of_Sup mynat  (λ s, sorry)

lemma fib_dvd_fib {m n : ℕ} (h : m ∣ n) : m.fib ∣ n.fib :=
begin
  sorry
end

def fib : mynat ⥤ mynat :=
{ obj := nat.fib,
  map := λ m n h, hom_of_le (fib_dvd_fib (le_of_hom h)),
  map_id' := λ _, rfl,
  map_comp' := λ a b c f g, by simp}

instance : category mynat := by apply_instance

instance : limits.has_finite_limits mynat := by apply_instance