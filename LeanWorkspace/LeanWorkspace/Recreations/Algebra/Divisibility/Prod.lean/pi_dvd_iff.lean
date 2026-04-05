import Mathlib

variable {ι G₁ G₂ : Type*} {G : ι → Type*} [Semigroup G₁] [Semigroup G₂] [∀ i, Semigroup (G i)]

theorem pi_dvd_iff {x y : ∀ i, G i} : x ∣ y ↔ ∀ i, x i ∣ y i := by
  simp_rw [dvd_def, funext_iff, Classical.skolem]; rfl

