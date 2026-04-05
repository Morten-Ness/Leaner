import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_of_s_rat_eq (v_eq_q : v = (↑q : K)) :
    ((of q).s.map (Pair.map ((↑))) : Stream'.Seq <| Pair K) = (of v).s := by
  ext n; rw [← GenContFract.coe_of_s_get?_rat_eq v_eq_q]; rfl

