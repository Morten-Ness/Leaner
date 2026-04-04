import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p ∈ s₁)
    (hp₂ : p ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  simp

