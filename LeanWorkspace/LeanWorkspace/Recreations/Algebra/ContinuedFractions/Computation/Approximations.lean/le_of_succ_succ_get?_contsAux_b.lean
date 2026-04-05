import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem le_of_succ_succ_get?_contsAux_b {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    b * ((of v).contsAux <| n + 1).b ≤ ((of v).contsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [GenContFract.of_partNum_eq_one (partNum_eq_s_a nth_s_eq), GenContFract.zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

