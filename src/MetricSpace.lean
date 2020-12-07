-- Metric space

import Metric

-- Example 1

noncomputable def MES_L1 : metric_space ℝ :=
{ dist := d_L1,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

-- Example 2

noncomputable def MES_L2 : metric_space ℝ :=
{ dist := d_L2,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

-- Example 3

#check RealPoint
#check d_taxicab -- d_taxicab : metric RealPoint

noncomputable def MES_taxicab : metric_space RealPoint :=
{ dist := d_taxicab,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

-- Example 4

#check d_euclid

noncomputable def MES_euclid : metric_space RealPoint :=
{ dist := d_euclid,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }