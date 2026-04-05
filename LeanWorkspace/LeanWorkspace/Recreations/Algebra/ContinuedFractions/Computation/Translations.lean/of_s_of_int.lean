import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

variable [IsStrictOrderedRing K]

theorem of_s_of_int (a : ℤ) : (of (a : K)).s = Stream'.Seq.nil := haveI h : ∀ n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [GenContFract.of_s_head_aux, GenContFract.IntFractPair.stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm

