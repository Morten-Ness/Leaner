import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem π_single (g : relations.G) :
    solution.π (Finsupp.single g 1) = solution.var g := by simp [Module.Relations.Solution.π]

