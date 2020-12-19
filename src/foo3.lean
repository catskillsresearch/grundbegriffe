import measure_theory.measure_space

open measure_theory

variables α β : Type*
variable MS1 : measurable_space α 
variable MS2 : measurable_space β 
variable μ_α : α → β
variable m_α : measure α 

#check @measure_theory.measure.map α β MS1 MS2 μ_α m_α 
#check measure_theory.measure.map μ_α m_α
