import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd := rfl

