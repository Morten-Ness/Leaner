import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem finrank_vectorSpan_range_add_one_le [Fintype ι] [Nonempty ι] (p : ι → P) :
    finrank k (vectorSpan k (Set.range p)) + 1 ≤ Fintype.card ι := (le_tsub_iff_right <| Nat.succ_le_iff.2 Fintype.card_pos).1 <| finrank_vectorSpan_range_le _ _
    (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 Fintype.card_pos).symm

