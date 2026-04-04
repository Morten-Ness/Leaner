import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

theorem AffineIndependent.finrank_vectorSpan_add_one [Fintype ι] [Nonempty ι] {p : ι → P}
    (hi : AffineIndependent k p) : finrank k (vectorSpan k (Set.range p)) + 1 = Fintype.card ι := by
  rw [hi.finrank_vectorSpan (tsub_add_cancel_of_le _).symm, tsub_add_cancel_of_le] <;>
    exact Fintype.card_pos

