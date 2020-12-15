import algebra.group_with_zero.defs
import data.nat.basic
import init.meta.tactic
import tactic
#check (by apply_instance: preorder ℕ)

lemma nat_le_trans (a b c : ℕ ) : a ≤ b → b ≤ c → a ≤ c := nat.le_trans

instance : preorder ℕ := {
  le := (≤),
  le_refl := nat.le_refl,
  le_trans := nat_le_trans,
}
