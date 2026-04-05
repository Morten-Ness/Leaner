import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toProd_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).toProd = -x.toProd := rfl

