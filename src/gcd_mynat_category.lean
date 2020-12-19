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

-- nat.gcd n m is the categorical product of n and m
-- nat.gcd n m is the pullback of n and m
-- nat.gcd n m is the inverse limit of n and m
-- nat.gcd n m is the equalizer of n and m

def mynat : Type := nat
def to_nat : mynat → nat := id
instance : has_dvd mynat := {dvd := λ a b, to_nat a ∣ b}

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

-- ℕ has a partial_order under divisibility
-- ℕ has a meet defined as n ⊓ m = nat.gcd n m 
-- ℕ is a meet semilattice

instance : has_Sup mynat := ⟨λ s, if h : s.finite then finset.sup (set.finite.to_finset h) id else (0: ℕ)⟩

instance : complete_lattice mynat := complete_lattice_of_Sup mynat  (λ s, sorry)

-- nat.fib preserves meets, where we define  "preserve meets" by  (nat.fib n)⊓ (nat.fib m) = nat.fib (n ⊓ m)
-- nat.fib is a meet semilattice homomorphism

lemma fib_dvd_fib {m n : ℕ} (h : m ∣ n) : m.fib ∣ n.fib :=
begin
  sorry
end

-- nat.fib is a functor because nat.gcd(nat.fib n, nat.fib m) = nat.fib(nat.gcd n m)
-- nat.fib is a continuous functor, because it preserves limits

def fib : mynat ⥤ mynat :=
{ obj := nat.fib,
  map := λ m n h, hom_of_le (fib_dvd_fib (le_of_hom h)),
  map_id' := λ _, rfl,
  map_comp' := λ a b c f g, by simp}

-- ℕ is a category
-- ℕ is also a complete category

instance : category mynat := by apply_instance

-- ℕ has a categorical limit

instance : limits.has_finite_limits mynat := by apply_instance