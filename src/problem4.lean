import tactic

def yadda : ℕ := 1

class is_golem (s : ℕ) : Prop :=
(three_mem : s=(3:ℕ))

#reduce yadda=3 -- 1 = 3

theorem yadda_not_golem : ¬ (is_golem yadda) := -- Thomas Browning
begin
  intro h1,
  have h2 : 1 = 3 := h1.three_mem,
  have h3 : 0 = 2 := nat.succ.inj h2,
  have h4 : 2 ≠ 0 := nat.succ_ne_zero 1,
  exact h4 h3.symm,
end
