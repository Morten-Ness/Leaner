import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem convs'Aux_succ_some {s : Stream'.Seq (Pair K)} {p : Pair K} (h : s.head = some p)
    (n : ℕ) : convs'Aux s (n + 1) = p.a / (p.b + convs'Aux s.tail n) := by
  simp [convs'Aux, h]

