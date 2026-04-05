import Mathlib

variable {K : Type*} {n : ℕ}

theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : ContFract K} :
    (↑c : GenContFract K).convs = (↑c : GenContFract K).convs' := by
  ext n
  apply GenContFract.convs_eq_convs'
  intro gp m _ s_nth_eq
  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
    (partNum_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| partDen_eq_s_b s_nth_eq⟩

