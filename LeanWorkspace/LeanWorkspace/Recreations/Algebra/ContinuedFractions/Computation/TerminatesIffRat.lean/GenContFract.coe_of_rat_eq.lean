import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_of_rat_eq (v_eq_q : v = (↑q : K)) :
    (⟨(of q).h, (of q).s.map (Pair.map (↑))⟩ : GenContFract K) = of v := by
  rcases gcf_v_eq : of v with ⟨h, s⟩; subst v
  obtain rfl : ↑⌊(q : K)⌋ = h := by injection gcf_v_eq
  simp [GenContFract.coe_of_s_rat_eq rfl, gcf_v_eq]

