import Mathlib

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' := ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩

