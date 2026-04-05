import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem fromQuotient_toQuotient (x : relations.G →₀ A) :
    solution.fromQuotient (relations.toQuotient x) = solution.π x := rfl

