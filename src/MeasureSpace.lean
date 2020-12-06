import measure_theory.measurable_space
import measure_theory.measure_space
import Measure

#check M

-- Measure space (S,Σ,μ)

instance M1_MS : measure_space M :=
{ to_measurable_space := M,
  volume := M_measure }