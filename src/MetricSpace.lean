-- Metric space

-- Metric Space: taxicab, euclidean

import data.real.basic topology.metric_space.basic

noncomputable theory

def metric_signature (α: Type) := α → α → ℝ 

class metric

def metric_space_instance (M : Type) (d : metric_signature M ) : metric_space (M) :=  
{ dist := d,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

def M : Type := ℝ × ℝ 

def d_taxicab : metric_signature M :=
    λ x y, (abs (x.1 - y.1)) + (abs (x.2 - y.2))

def d_euclid : metric_signature M := 
    λ x y, real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2),

def S_taxicab := metric_space_instance M d_taxicab

def S_euclid:= metric_space_instance M d_euclid

#check S_taxicab -- S_taxicab : metric_space M
#check S_euclid  -- S_euclid : metric_space M
dR: ℝ × ℝ → [0,∞)
μ: B(M) → [0,∞)
f⁻¹: Σ → A
λ⋆ : L(ℝ) → [0,∞)
(Ω,A,P)
μ⨯ : Σ → [0,1]
(ℝ, B(ℝ), μ_x, F_X)

import topology.metric_space.basic
variable M: Type
variable S: metric_space(M)

-- patrick massot

import topology.metric_space.basic

noncomputable theory


def m1 : metric_space (ℝ × ℝ) :=
{ dist := λ x y, max (abs (x.1 - y.1)) (abs (x.2 - y.2)),
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

def m2 : metric_space (ℝ × ℝ) :=
{ dist := λ x y, real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2),
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

def t1 : topological_space (ℝ × ℝ) := m1.to_uniform_space.to_topological_space

def t2 : topological_space (ℝ × ℝ) := m2.to_uniform_space.to_topological_space

local notation `cont` := @continuous _ _

variables f : ℝ × ℝ → ℝ × ℝ

-- IMPORTANT!!

#check cont t1 t2 f

def MetricSpace := Σ α, metric_space α

example : MetricSpace := ⟨ℝ, by apply_instance⟩

-- Another try

import data.real.basic topology.metric_space.basic

noncomputable theory

def d1 : ℝ × ℝ → ℝ × ℝ → ℝ :=
    λ x y, max (abs (x.1 - y.1)) (abs (x.2 - y.2))

def m1 : metric_space (ℝ × ℝ) :=
{ dist := d1,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

variables a b : ℝ × ℝ

#check a            -- a : ℝ × ℝ
#check b            -- b : ℝ × ℝ
#check m1.dist      -- dist : ℝ × ℝ → ℝ × ℝ → ℝ
#check m1.dist a b -- ERROR
#check d1          -- d1 : ℝ × ℝ → ℝ × ℝ → ℝ
#check d1 a b   -- d1 a b : ℝ

-- me again

noncomputable theory

def metric_signature (α: Type) := α → α → ℝ

def metric_space_instance (M : Type) (d : metric_signature M ) : metric_space (M) :=
{ dist := d,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

def M : Type := ℝ × ℝ

def d_taxicab : metric_signature M :=
    λ x y, (abs (x.1 - y.1)) + (abs (x.2 - y.2))

def d_euclid : metric_signature M :=
    λ x y, real.sqrt ((x.1 - y.1)^2 + (x.2 - y.2)^2),

def S_taxicab := metric_space_instance M d_taxicab

def S_euclid:= metric_space_instance M d_euclid

#check S_taxicab -- S_taxicab : metric_space M
#check S_euclid  -- S_euclid : metric_space M

-- Yakov

import data.real.basic topology.metric_space.basic

noncomputable theory

def metric_signature (α: Type) := α → α → ℝ

def metric_space_instance (M : Type) (d : metric_signature M ) : metric_space (M) :=
{ dist := d,
  dist_self := sorry,
  eq_of_dist_eq_zero := sorry,
  dist_comm := sorry,
  dist_triangle := sorry }

notation `M` := ℝ × ℝ

def d_nonsensical : metric_signature M :=
  λ x y, 1

def S_nonsensical : metric_space M := metric_space_instance M d_nonsensical

#check S_nonsensical  -- S_nonsensical : metric_space M

#exit
