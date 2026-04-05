import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_inf_of_mem {s₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) :
    (s₁ ⊓ s₂).direction = s₁.direction ⊓ s₂.direction := by
  ext v
  rw [Submodule.mem_inf, ← AffineSubspace.vadd_mem_iff_mem_direction v h₁, ← AffineSubspace.vadd_mem_iff_mem_direction v h₂, ←
    AffineSubspace.vadd_mem_iff_mem_direction v ((AffineSubspace.mem_inf_iff p s₁ s₂).2 ⟨h₁, h₂⟩), AffineSubspace.mem_inf_iff]

