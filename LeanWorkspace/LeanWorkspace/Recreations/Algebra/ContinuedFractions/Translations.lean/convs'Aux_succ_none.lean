import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem convs'Aux_succ_none {s : Stream'.Seq (Pair K)} (h : s.head = none) (n : ℕ) :
    convs'Aux s (n + 1) = 0 := by simp [convs'Aux, h]

