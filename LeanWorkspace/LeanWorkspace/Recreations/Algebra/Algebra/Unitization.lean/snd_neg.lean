import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem snd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).snd = -x.snd := rfl

