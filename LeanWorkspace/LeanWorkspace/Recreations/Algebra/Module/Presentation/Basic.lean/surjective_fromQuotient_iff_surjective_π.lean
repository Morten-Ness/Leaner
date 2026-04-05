import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem surjective_fromQuotient_iff_surjective_π :
    Function.Surjective solution.fromQuotient ↔ Function.Surjective solution.π := by
  simpa only [← Module.Relations.Solution.fromQuotient_comp_toQuotient] using
    (Function.Surjective.of_comp_iff (f := solution.fromQuotient)
      Module.Relations.surjective_toQuotient relations).symm

