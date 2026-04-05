import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (π : (relations.G →₀ A) →ₗ[A] M) (hπ : ∀ (r : relations.R), π (relations.relation r) = 0)

theorem ofπ_π : (Module.Relations.Solution.ofπ Module.Relations.Solution.π hπ).π = Module.Relations.Solution.π := by ext; simp [Module.Relations.Solution.ofπ]

