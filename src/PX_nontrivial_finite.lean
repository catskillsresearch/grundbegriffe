import data.finset.basic
def X := fin 3
instance : nontrivial X := fin.nontrivial
instance : nontrivial (set X) := nontrivial_of_ne _ _ set.empty_ne_univ.symm
