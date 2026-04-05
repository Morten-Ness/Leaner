import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
    { a := 1
      b := p.b }) := by
  rw [of, IntFractPair.seq1]
  simp only [Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ, Stream'.get, Option.map.eq_def]
  split <;> simp_all only [Option.bind_some, Option.bind_none, Function.comp_apply]

