import Mathlib

variable {A : Type v} [Ring A]

variable {M : Type w} [AddCommGroup M] [Module A M]

theorem lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m := rfl

