import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [AffineSubspace.direction_affineSpan_insert hp₁]
