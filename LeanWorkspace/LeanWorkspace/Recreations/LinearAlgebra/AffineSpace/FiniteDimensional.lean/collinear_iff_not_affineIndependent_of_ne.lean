import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_iff_not_affineIndependent_of_ne {p : Fin 3 → P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Collinear k ({p i₁, p i₂, p i₃} : Set P) ↔ ¬AffineIndependent k p := (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).not_left.symm

