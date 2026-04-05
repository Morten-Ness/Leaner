import Mathlib

variable {K : Type*} {n : ℕ}

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

variable [DivisionRing K]

theorem succ_nth_conv'_eq_squashGCF_nth_conv' :
    g.convs' (n + 1) = (GenContFract.squashGCF g n).convs' n := by
  cases n with
  | zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, GenContFract.squashGCF, convs', convs'Aux, Stream'.Seq.head]
  | succ =>
    simp only [GenContFract.succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq, convs',
      GenContFract.squashGCF]

