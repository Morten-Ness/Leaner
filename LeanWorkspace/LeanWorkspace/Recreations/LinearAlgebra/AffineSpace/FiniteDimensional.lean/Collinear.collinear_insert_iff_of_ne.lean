import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Collinear.collinear_insert_iff_of_ne {s : Set P} (h : Collinear k s) {p₁ p₂ p₃ : P}
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₃ : p₂ ≠ p₃) :
    Collinear k (insert p₁ s) ↔ Collinear k ({p₁, p₂, p₃} : Set P) := by
  have hv : vectorSpan k (insert p₁ s) = vectorSpan k ({p₁, p₂, p₃} : Set P) := by
    conv_rhs => rw [← direction_affineSpan, ← affineSpan_insert_affineSpan]
    rw [← direction_affineSpan, ← affineSpan_insert_affineSpan, h.affineSpan_eq_of_ne hp₂ hp₃ hp₂p₃]
  rw [Collinear, Collinear, hv]

