import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

theorem ofQuotient_isPresentation : (Module.Relations.Solution.ofQuotient relations).IsPresentation where
  bijective := by
    simpa only [Module.Relations.Solution.ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

