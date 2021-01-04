import algebra.ring.basic
import ring_theory.subring

/- universe u
variable α : Type u
variable R : α 

def q6_pred (s : set R) : Prop := 
  ∃ (s' : subring R), ↑s' = s ∧ integral_domain s' -/