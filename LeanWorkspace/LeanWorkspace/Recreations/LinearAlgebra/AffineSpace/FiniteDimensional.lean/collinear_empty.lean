import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

theorem collinear_empty : Collinear k (∅ : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_empty]
  simp

