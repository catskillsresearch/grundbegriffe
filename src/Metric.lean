import data.real.basic
import topology.metric_space.basic

-- Metric: α → α → ℝ

abbreviation metric (α: Type) := α → α → ℝ

-- Example 1

noncomputable def d_L1 : metric ℝ := λ x y, abs (x - y)

-- Example 2

noncomputable def d_L2 : metric ℝ := λ x y, real.sqrt ((x - y)^2)

-- Example 3

abbreviation RealPoint : Type := ℝ × ℝ -- real points

noncomputable def d_taxicab : metric RealPoint := λ x y, (abs (x.1 - y.1)) + (abs (x.2 - y.2))

#check d_taxicab -- d_taxicab : metric RealPoint

-- Example 4

noncomputable def d_euclid : metric RealPoint := λ x y, real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2)

#check d_euclid -- d_euclid : metric RealPoint