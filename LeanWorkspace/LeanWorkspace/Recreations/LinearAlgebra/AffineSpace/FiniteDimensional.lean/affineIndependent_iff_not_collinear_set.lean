import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem affineIndependent_iff_not_collinear_set {p₁ p₂ p₃ : P} :
    AffineIndependent k ![p₁, p₂, p₃] ↔ ¬Collinear k ({p₁, p₂, p₃} : Set P) := by
  rw [affineIndependent_iff_not_collinear]
  simp_rw [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, insert_empty_eq]

