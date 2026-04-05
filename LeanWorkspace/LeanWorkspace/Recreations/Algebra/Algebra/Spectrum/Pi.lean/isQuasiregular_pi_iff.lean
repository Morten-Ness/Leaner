import Mathlib

variable {ι A B R : Type*} {κ : ι → Type*}

theorem isQuasiregular_pi_iff [∀ i, NonUnitalSemiring (κ i)] (x : ∀ i, κ i) :
    IsQuasiregular x ↔ ∀ i, IsQuasiregular (x i) := by
  simp only [isQuasiregular_iff', ← isUnit_map_iff (PreQuasiregular.toPi κ), Pi.isUnit_iff]
  congr!

