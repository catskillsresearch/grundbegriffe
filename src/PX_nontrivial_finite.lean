import data.finset.basic

def X := fin 3

instance : nontrivial X := fin.nontrivial

instance : nontrivial (set X) := 
begin
  refine nontrivial_of_ne _ _ _,
  exact set.univ,
  exact ∅ ,
  exact set.empty_ne_univ.symm,
end
