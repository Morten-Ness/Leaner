import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem π_comp_map_apply (x : relations.R →₀ A) : solution.π (relations.map x) = 0 := by
  change solution.π.comp relations.map x = 0
  rw [Module.Relations.Solution.π_comp_map, LinearMap.zero_apply]

