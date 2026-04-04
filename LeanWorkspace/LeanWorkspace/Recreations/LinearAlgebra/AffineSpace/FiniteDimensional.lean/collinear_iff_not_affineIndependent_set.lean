import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_iff_not_affineIndependent_set {p₁ p₂ p₃ : P} :
    Collinear k ({p₁, p₂, p₃} : Set P) ↔ ¬AffineIndependent k ![p₁, p₂, p₃] := affineIndependent_iff_not_collinear_set.not_left.symm

