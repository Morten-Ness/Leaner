import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).fst = n := rfl

