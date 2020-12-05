import data.finset.basic
import tactic.dec_trivial

-- {1,2,3}

def S1A : ({1, 2, 3} : finset ℕ)
def S1B : set ℕ := ({1, 2, 3} : finset ℕ)
def S2 : set ℕ := {n : ℕ | 0 < n ∧ n ≤ 3}
def S3 : Type := fin 3

example : 1 ∈ S := set.left_mem_Icc.mpr (show 1 ≤ 3, from dec_trivial)
