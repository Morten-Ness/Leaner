import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem affineIndependent_iff_affineIndependent_collinear_ne {p₁ p₂ p₃ p : P}
    (hcol : Collinear k {p₂, p, p₃}) (hne1 : p₂ ≠ p) (hne2 : p₂ ≠ p₃) :
    AffineIndependent k ![p₁, p₂, p] ↔ AffineIndependent k ![p₁, p₂, p₃] := by
  refine ⟨fun h ↦ affineIndependent_of_affineIndependent_collinear_ne h hcol hne2,
    fun h ↦ affineIndependent_of_affineIndependent_collinear_ne h ?_ hne1⟩
  convert hcol using 1
  aesop

