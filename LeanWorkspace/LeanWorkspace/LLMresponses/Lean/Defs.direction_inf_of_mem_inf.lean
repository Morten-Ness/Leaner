FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)
variable (P)
variable {k V P}
variable (k V) {p₁ p₂ : P}
variable (P) in
variable {P}

theorem direction_inf_of_mem_inf {s₁ s₂ : AffineSubspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  rw [← AffineSubspace.direction_affineSpan_insert_eq_direction (s := s₁ ⊓ s₂) h]
  rw [← AffineSubspace.direction_affineSpan_insert_eq_direction (s := s₁) h.1]
  rw [← AffineSubspace.direction_affineSpan_insert_eq_direction (s := s₂) h.2]
  simp [AffineSubspace.affineSpan_insert_eq_sup, inf_sup_right]
