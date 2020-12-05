-- Random variable (Ω,A,P)→(S,Σ) from probability space to measure space
-- V: (X, Σ) \→  (Y,d) be a Y-valued random variable

import measure_theory.borel_space

variables (X Y : Type) [measurable_space X] [measurable_space Y] [metric_space Y] [borel_space Y] (x : X → Y)
#check measurable x -- x is a Y-valued RV on X

Let (𝑋,Σ) be a measure space.

Let (𝑌,𝑑) be a metric space.

Let 𝑥 be a map from 𝑋 to 𝑌 such that (inv x)(𝐵)∈Σ for any Borel set 𝐵 in 𝑌 .

We say that 𝑥:(𝑋,Σ)→(𝑌,𝑑) is a 𝑌 -valued random function and 𝑥 is a Σ -measurable function.

We say that 𝑥 is a 𝑌 -valued random variable iff

(inv x)(𝑂)∈Σ for any open set 𝑂
(inv x)(𝑆)∈Σ for any closet set 𝑆
If 𝑌=ℜ , then {𝑤∈𝑋:𝑥(𝑤)≤𝛼}∈Σ for any 𝛼∈ℜ ."

import measure_theory.borel_space

variables (X Y : Type) [measurable_space X]
  [measurable_space Y] [metric_space Y] [borel_space Y] (x : X → Y)

#check measurable x -- x is a Y-valued RV on X

