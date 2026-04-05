import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

theorem of_linearEquiv (e : M ≃ₗ[A] N) : (solution.postcomp e.toLinearMap).IsPresentation where
  bijective := by
    have : (solution.postcomp e.toLinearMap).fromQuotient =
      e.toLinearMap.comp (solution.fromQuotient) := by aesop
    rw [this, LinearMap.coe_comp, LinearEquiv.coe_coe]
    exact Function.Bijective.comp e.bijective h.bijective

