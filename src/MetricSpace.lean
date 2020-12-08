import data.real.basic
import topology.metric_space.basic
import Metric

-- Metric space

-- Example 1

noncomputable def MES_L1 : metric_space ℝ :=
{ dist := d_L1,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L1 -- MES_L1 : metric_space ℝ

-- Example 2

noncomputable def MES_L2 : metric_space ℝ :=
{ dist := d_L2,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L2 -- MES_L2 : metric_space ℝ

-- Example 3

noncomputable def MES_taxicab : metric_space RealPoint :=
{ dist := d_taxicab,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_taxicab -- MES_taxicab : metric_space RealPoint

-- Example 4

noncomputable def MES_euclid: metric_space RealPoint :=
{ dist := d_euclid,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_euclid -- MES_taxicab : metric_space RealPoint