import Mathlib

section

variable {ι G₁ G₂ : Type*} {G : ι → Type*} [Semigroup G₁] [Semigroup G₂] [∀ i, Semigroup (G i)]

theorem pi_dvd_iff {x y : ∀ i, G i} : x ∣ y ↔ ∀ i, x i ∣ y i := by
  simp_rw [dvd_def, funext_iff, Classical.skolem]; rfl

end

section

variable {ι G₁ G₂ : Type*} {G : ι → Type*} [Semigroup G₁] [Semigroup G₂] [∀ i, Semigroup (G i)]

theorem prod_dvd_iff {x y : G₁ × G₂} :
    x ∣ y ↔ x.1 ∣ y.1 ∧ x.2 ∣ y.2 := by
  cases x; cases y
  simp only [dvd_def, Prod.exists, Prod.mk_mul_mk, Prod.mk.injEq,
    exists_and_left, exists_and_right]

end
