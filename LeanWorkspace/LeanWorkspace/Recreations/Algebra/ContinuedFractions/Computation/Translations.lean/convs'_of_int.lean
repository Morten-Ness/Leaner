import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

variable [IsStrictOrderedRing K]

theorem convs'_of_int (a : ℤ) : (of (a : K)).convs' n = a := by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, GenContFract.of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs', GenContFract.of_h_eq_floor, floor_intCast, add_eq_left]
    exact convs'Aux_succ_none ((GenContFract.of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _

