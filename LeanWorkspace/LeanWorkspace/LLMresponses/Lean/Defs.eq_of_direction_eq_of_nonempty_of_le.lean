FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem eq_of_direction_eq_of_nonempty_of_le {s₁ s₂ : AffineSubspace k P}
    (hd : s₁.direction = s₂.direction) (hn : (s₁ : Set P).Nonempty) (hle : s₁ ≤ s₂) : s₁ = s₂ := by
  rcases hn with ⟨p, hp⟩
  have hp₂ : p ∈ s₂ := hle hp
  apply le_antisymm hle
  intro q hq₂
  have hdir₂ : q -ᵥ p ∈ s₂.direction := s₂.vsub_mem_direction hq₂ hp₂
  rw [← hd] at hdir₂
  have hq₁ : (q -ᵥ p) +ᵥ p ∈ s₁ := s₁.vadd_mem_of_mem_direction hp hdir₂
  simpa using hq₁
