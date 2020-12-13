import algebra.group.defs
import data.finset.basic
import data.nat.basic

instance X_is_nontrivial : nontrivial (fin 3) := fin.nontrivial
#check X_is_nontrivial --X_is_nontrivial : nontrivial X

instance X_has_add : has_add (fin 3):= fin.has_add
#check X_has_add -- X_has_add : has_add X
