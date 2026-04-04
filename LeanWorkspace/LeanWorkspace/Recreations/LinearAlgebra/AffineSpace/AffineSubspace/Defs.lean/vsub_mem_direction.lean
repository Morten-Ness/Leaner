import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vsub_mem_direction {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    p₁ -ᵥ p₂ ∈ s.direction := vsub_mem_vectorSpan k hp₁ hp₂

