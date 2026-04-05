import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [AddCommMonoidWithOne R]

theorem natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    (#{x ∈ s | p x} : R) = ∑ a ∈ s, if p a then (1 : R) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]

