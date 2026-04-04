import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem Parallel.direction_eq {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) :
    s₁.direction = s₂.direction := by
  rcases h with ⟨v, rfl⟩
  simp

