import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

theorem collinear_singleton (p : P) : Collinear k ({p} : Set P) := by
  rw [collinear_iff_rank_le_one, vectorSpan_singleton]
  simp

