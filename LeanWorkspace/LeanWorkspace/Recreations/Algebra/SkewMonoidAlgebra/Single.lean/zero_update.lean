import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem zero_update : Function.update 0 a b = single a b := by
  simp [Function.update]

