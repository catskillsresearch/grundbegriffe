import data.real.basic
import topology.metric_space.basic

-- Example 1

noncomputable def d_L1 := λ (x y : ℝ), abs (x - y)

noncomputable def R_has_dist_L1 : has_dist ℝ := ⟨ d_L1 ⟩ 

noncomputable def MES_L1 : metric_space ℝ :=
{ dist := d_L1,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L1 -- MES_L1 : metric_space ℝ

-- Example 2

noncomputable def d_L2 := λ (x y : ℝ), real.sqrt ((x - y)^2)

noncomputable def R_has_dist_l2 : has_dist ℝ := ⟨ d_L1 ⟩ 

noncomputable def MES_L2 : metric_space ℝ :=
{ dist := d_L2,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_L2 -- MES_L2 : metric_space ℝ

-- Example 3

abbreviation RealPoint : Type := ℝ × ℝ -- real points

noncomputable def d_taxicab := λ (x y : RealPoint), (abs (x.1 - y.1)) + (abs (x.2 - y.2))

noncomputable def RealPoint_has_dist_taxicab : has_dist RealPoint := ⟨ d_taxicab ⟩ 

noncomputable def MES_taxicab : metric_space RealPoint :=
{ dist := d_taxicab,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_taxicab -- MES_taxicab : metric_space RealPoint

-- Example 4

noncomputable def d_euclid  := λ (x y : RealPoint), real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2)

noncomputable def RealPoint_has_dist_euclid : has_dist RealPoint := ⟨ d_taxicab ⟩ 

noncomputable def MES_euclid: metric_space RealPoint :=
{ dist := d_euclid,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

#check MES_euclid -- MES_taxicab : metric_space RealPoint