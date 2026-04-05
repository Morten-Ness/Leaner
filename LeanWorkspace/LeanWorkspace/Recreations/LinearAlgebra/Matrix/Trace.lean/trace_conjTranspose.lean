import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) : Matrix.trace Aᴴ = star (Matrix.trace A) := (star_sum _ _).symm

