import Mathlib

open scoped Pointwise Ring

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  ext
  simp

