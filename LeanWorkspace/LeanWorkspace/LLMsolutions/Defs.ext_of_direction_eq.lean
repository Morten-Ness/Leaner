FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem ext_of_direction_eq {s₁ s₂ : AffineSubspace k P} (hd : s₁.direction = s₂.direction)
    (hn : ((s₁ : Set P) ∩ s₂).Nonempty) : s₁ = s₂ := by
  rcases hn with ⟨p, hp1, hp2⟩
  ext q
  constructor
  · intro hq
    have hdir : q -ᵥ p ∈ s₁.direction := s₁.vsub_mem_direction hp1 hq
    rwa [hd, s₂.vadd_mem_iff_mem_direction hp2] at hdir
  · intro hq
    have hdir : q -ᵥ p ∈ s₂.direction := s₂.vsub_mem_direction hp2 hq
    rwa [← hd, s₁.vadd_mem_iff_mem_direction hp1] at hdir
