import Mathlib

open scoped BigOperators

variable {ι H F G : Type*}

variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]

theorem balance_apply (f : ι → G) (x : ι) : Fintype.balance f x = f x - 𝔼 y, f y := rfl

