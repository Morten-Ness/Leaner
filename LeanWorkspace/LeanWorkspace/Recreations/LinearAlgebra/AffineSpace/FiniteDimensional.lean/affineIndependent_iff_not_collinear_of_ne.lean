import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem affineIndependent_iff_not_collinear_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    AffineIndependent k p ↔ ¬Collinear k ({p i₁, p i₂, p i₃} : Set P) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {i₁, i₂, i₃} := by decide +revert
  rw [affineIndependent_iff_not_collinear, ← Set.image_univ, ← Finset.coe_univ, hu,
    Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_pair]

