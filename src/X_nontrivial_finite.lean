-- nontrivial {0,1,2}
import data.finset.basic
def X := fin 3
instance X_nontrivial : nontrivial X := fin.nontrivial
#check X_nontrivial --X_nontrivial : nontrivial X
