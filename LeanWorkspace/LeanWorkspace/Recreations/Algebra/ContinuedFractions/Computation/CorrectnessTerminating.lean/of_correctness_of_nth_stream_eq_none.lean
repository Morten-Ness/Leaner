import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convs (n - 1) := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    let g := of v
    change v = g.convs n
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        -- IntFractPair.stream v 0 ≠ none
        have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convs (n' + 1) = g.convs n' :=
          convs_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using
        GenContFract.compExactValue_correctness_of_stream_eq_some nth_stream_eq

