import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem affineIndependent_iff_not_collinear {p : Fin 3 → P} :
    AffineIndependent k p ↔ ¬Collinear k (Set.range p) := by
  rw [collinear_iff_finrank_le_one,
    affineIndependent_iff_not_finrank_vectorSpan_le k p (Fintype.card_fin 3)]

