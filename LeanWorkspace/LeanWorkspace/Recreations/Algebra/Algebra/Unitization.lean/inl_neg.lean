import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_neg [Neg R] [AddGroup A] (r : R) : (Unitization.inl (-r) : Unitization R A) = -Unitization.inl r := Unitization.ext rfl neg_zero.symm

