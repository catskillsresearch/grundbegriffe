-- Probability measure p: Σ → [0,1]

import measure_theory.measure_space
import measure_theory.borel_space
import measure_theory.lebesgue_measure
import data.set.intervals.basic

open measure_theory

#check real.borel_space -- real.borel_space : borel_space ℝ
#check measure_theory.probability_measure -- probability_measure : measure ?M_1 → Prop

-- Q1: 

def Icc01 : set ℝ := set.Icc 0 1 -- [0,1]

-- Q1: Borel sets of Icc01

#check real.volume_Icc -- real.volume_Icc : ⇑measure_theory.measure_space.volume (set.Icc ?M_1 ?M_2) = ennreal.of_real (?M_2 - ?M_1)
#check real.volume_Icc (set.Icc 0 1)
#check measure_space
#check real.measure_space.volume
