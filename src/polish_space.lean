import topology.metric_space.basic

open topological_space

structure polish_space (α : Type*) extends uniform_space α :=
(is_complete: complete_space α )
(is_second_countable: second_countable_topology α)
