import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

variable [IsStrictOrderedRing K]

theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s := Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ GenContFract.of_s_succ v n

