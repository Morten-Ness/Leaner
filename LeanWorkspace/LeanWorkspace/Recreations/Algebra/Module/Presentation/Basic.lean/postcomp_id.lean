import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

variable {N : Type v'} [AddCommGroup N] [Module A N] (f : M →ₗ[A] N)

theorem postcomp_id : solution.postcomp LinearMap.id = solution := rfl

