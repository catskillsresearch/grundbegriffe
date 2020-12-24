--import probability_space
import measure_theory.lebesgue_measure
import topology.compact_open

@[derive [topological_space, has_coe_to_fun]]
def Brownian_event_space := C(nnreal, ℝ)
local notation `Ω` := Brownian_event_space

noncomputable instance : measurable_space Ω := borel _
instance : borel_space Ω := ⟨rfl⟩

def interval (n : ℕ ) (I : (fin n) → ℝ × ℝ) (k: (fin n)) := set.Ioo (I k).1 (I k).2

def cylinder_set (n : ℕ) (t : fin n → nnreal) 
                 (I : (fin n) → ℝ × ℝ ) :=
  {ω : Brownian_event_space | ∀ k : fin n, (ω (t k) ∈ (interval n I k))}

#check cylinder_set -- : Π (n : ℕ), (fin n → nnreal) → (fin n → ℝ × ℝ) → set Ω