import data.finset.basic

-- A set with 3 elements

def S1A : finset ℕ := {1, 2, 3} 
#check S1A -- S1A : finset ℕ

def S1B : set ℕ := ({1, 2, 3} : finset ℕ)
#check S1B -- S1B : set ℕ

def S2 : set ℕ := {n : ℕ | 0 < n ∧ n ≤ 3}
#check S2 -- S2 : set ℕ

example : 1 ∈ S2 := 
  set.left_mem_Icc.mpr (show 1 ≤ 3, from dec_trivial)

def S3 : set (fin 3) := ⊤ 
#check S3 -- S3 : set (fin 3)

def S3A : set ℕ := S3
