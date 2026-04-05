import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v : K) (n : ℕ)

theorem exists_gcf_pair_rat_eq_nth_conts :
    ∃ conts : Pair ℚ, (of v).conts n = (conts.map (↑) : Pair K) := by
  rw [nth_cont_eq_succ_nth_contAux]; exact exists_gcf_pair_rat_eq_of_nth_contsAux v <| n + 1

