-- Borel σ-algebra B((a,b)) for a b : ℝ

import measure_theory.measurable_space
import measure_theory.borel_space

#check (by apply_instance : measurable_space (set.Ioo (0:ℝ) 1))
#check (by apply_instance : measurable_space (set.Icc (0:ℝ) 1))
#check (by apply_instance : measurable_space (set.Ici (0:ℝ)))
