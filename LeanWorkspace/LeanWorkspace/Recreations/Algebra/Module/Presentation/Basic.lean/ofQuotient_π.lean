import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

theorem ofQuotient_π : (Module.Relations.Solution.ofQuotient relations).π = Submodule.mkQ _ := Module.Relations.Solution.ofπ_π _ _

