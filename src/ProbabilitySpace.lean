-- Let(X, Σ, P) be a probability space
-- where (X, Σ) is a measure space
-- and P: (X, Σ) → [0,1] is a probability measure

structure is_probability_space {X: Type *} (ΩA: measure_space X) (P: probability_measure ΩA) := ()

def is_probability_space.sample_space {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A):= X
def is_probability_space.event_space {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A) := A
def is_probability_space.probability_measure {X: Type*} {A : set X → Prop} (XA : is_σ_algebra X A) := A
