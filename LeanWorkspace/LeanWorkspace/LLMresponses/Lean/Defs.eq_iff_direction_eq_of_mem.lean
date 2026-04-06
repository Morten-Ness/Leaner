FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem eq_iff_direction_eq_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁)
    (h₂ : p ∈ s₂) : s₁ = s₂ ↔ s₁.direction = s₂.direction := by
  constructor
  · intro h
    simp [h]
  · intro hdir
    ext q
    rw [AffineSubspace.vsub_right_mem_direction_iff_mem h₂, AffineSubspace.vsub_right_mem_direction_iff_mem h₁]
    simpa [hdir] using Iff.rfl
