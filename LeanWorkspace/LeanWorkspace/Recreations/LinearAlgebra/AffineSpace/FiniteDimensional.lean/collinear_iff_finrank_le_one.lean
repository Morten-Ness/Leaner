import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem collinear_iff_finrank_le_one {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Collinear k s ↔ finrank k (vectorSpan k s) ≤ 1 := by
  have h := collinear_iff_rank_le_one k s
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Collinear.finrank_le_one, _⟩ := collinear_iff_finrank_le_one

