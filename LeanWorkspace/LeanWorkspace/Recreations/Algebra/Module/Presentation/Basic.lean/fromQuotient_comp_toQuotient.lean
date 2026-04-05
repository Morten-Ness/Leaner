import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem fromQuotient_comp_toQuotient :
    solution.fromQuotient.comp relations.toQuotient = solution.π := rfl

