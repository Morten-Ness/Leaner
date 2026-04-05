import Mathlib

variable {R M : Type*}

variable (A : Type*) [AddCommGroup A] (n : ℤ)

theorem torsionBy.neg : A[-n] = A[n] := by
  ext a
  simp

