import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

theorem ofQuotient_fromQuotient : (Module.Relations.Solution.ofQuotient relations).fromQuotient = .id := by aesop

