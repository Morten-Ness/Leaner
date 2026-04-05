import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem terminates_iff_rat (v : K) : (of v).Terminates ↔ ∃ q : ℚ, v = (q : K) := Iff.intro
    (fun terminates_v : (of v).Terminates =>
      show ∃ q : ℚ, v = (q : K) from GenContFract.exists_rat_eq_of_terminates terminates_v)
    fun exists_q_eq_v : ∃ q : ℚ, v = (↑q : K) =>
    Exists.elim exists_q_eq_v fun q => fun v_eq_q : v = ↑q =>
      have : (of q).Terminates := GenContFract.terminates_of_rat q
      (GenContFract.of_terminates_iff_of_rat_terminates v_eq_q).mpr this

