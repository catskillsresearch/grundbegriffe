import data.finset.basic

-- A set with 3 elements

def S1A : finset ℕ := {1, 2, 3} 
def S1B : set ℕ := ({1, 2, 3} : finset ℕ)
def S2 : set ℕ := {n : ℕ | 0 < n ∧ n ≤ 3}
def S3 : set (fin 3) := ⊤ 

#check S1A
#check S1B
#check S2
#check S3

example : 1 ∈ S2 := 
  set.left_mem_Icc.mpr (show 1 ≤ 3, from dec_trivial)


-- docs#measure_theory.measure.count in mathlib
-- the proof that fin n has size n is docs#fintype.card_fin
-- if the set is finite you can use finset.card to get the cardinality
-- you can also use cardinal.mk to get the cardinality of an infinite set but for measures you really just want this to cap out at infinity so the infinite sum on ennreal is the easiest thing to implement
-- the proof that fin n has size n is docs#fintype.card_fin