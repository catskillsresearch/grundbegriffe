import measure_theory.lebesgue_measure
import measure_theory.borel_space
import data.set.intervals.basic
import measure_theory.measure_space

open measure_theory

noncomputable theory

def I : Type* := set.Icc (0 : ℝ) 1
instance foo0 : topological_space I := by {unfold I, apply_instance}
instance foo1 : measurable_space I := borel I
instance foo2 : borel_space I := ⟨rfl⟩
#check foo2

def B01 : borel_space I := by apply_instance -- now it works.
#check B01

def μ := measure_theory.real.measure_space.volume
#check μ -- μ : measure_theory.measure ℝ

#check probability_measure μ