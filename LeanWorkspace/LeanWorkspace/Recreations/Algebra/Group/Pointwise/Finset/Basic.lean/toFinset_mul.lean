import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] {s t : Set α}

theorem toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] :
    (s * t).toFinset = s.toFinset * t.toFinset := toFinset_image2 _ _ _

