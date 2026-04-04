import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  rw [AffineSubspace.coe_direction_eq_vsub_set ⟨p, hp⟩]
  refine le_antisymm ?_ ?_
  · rintro v ⟨p₁, hp₁, p₂, hp₂, rfl⟩
    exact ⟨(p₁ -ᵥ p₂) +ᵥ p,
      AffineSubspace.vadd_mem_of_mem_direction (AffineSubspace.vsub_mem_direction hp₁ hp₂) hp, vadd_vsub _ _⟩
  · rintro v ⟨p₂, hp₂, rfl⟩
    exact ⟨p₂, hp₂, p, hp, rfl⟩

