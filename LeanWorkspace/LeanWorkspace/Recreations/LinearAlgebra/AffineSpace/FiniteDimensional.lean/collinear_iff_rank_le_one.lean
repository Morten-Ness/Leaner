import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem collinear_iff_rank_le_one (s : Set P) :
    Collinear k s ↔ Module.rank k (vectorSpan k s) ≤ 1 := Iff.rfl

