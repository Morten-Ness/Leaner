import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).snd = 0 := rfl

