import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (π : (relations.G →₀ A) →ₗ[A] M) (hπ : π.comp relations.map = 0)

theorem ofπ'_π : (Module.Relations.Solution.ofπ' Module.Relations.Solution.π hπ).π = Module.Relations.Solution.π := by simp [Module.Relations.Solution.ofπ']

