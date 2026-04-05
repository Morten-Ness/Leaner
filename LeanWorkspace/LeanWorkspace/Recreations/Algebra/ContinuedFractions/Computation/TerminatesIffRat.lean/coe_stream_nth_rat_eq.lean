import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem coe_stream_nth_rat_eq (v_eq_q : v = (↑q : K)) (n : ℕ) :
    ((GenContFract.IntFractPair.stream q n).map (mapFr (↑)) : Option <| GenContFract.IntFractPair K) =
      GenContFract.IntFractPair.stream v n := by
  induction n with
  | zero =>
    simp only [GenContFract.IntFractPair.stream, Option.map_some, GenContFract.IntFractPair.coe_of_rat_eq v_eq_q]
  | succ n IH =>
    rw [v_eq_q] at IH
    cases stream_q_nth_eq : GenContFract.IntFractPair.stream q n with
    | none => simp [GenContFract.IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq]
    | some ifp_n =>
      obtain ⟨b, fr⟩ := ifp_n
      rcases Decidable.em (fr = 0) with fr_zero | fr_ne_zero
      · simp [GenContFract.IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_zero]
      · replace IH : some (GenContFract.IntFractPair.mk b (fr : K)) = GenContFract.IntFractPair.stream (↑q) n := by
          rwa [stream_q_nth_eq] at IH
        have : (fr : K)⁻¹ = ((fr⁻¹ : ℚ) : K) := by norm_cast
        have coe_of_fr := GenContFract.IntFractPair.coe_of_rat_eq this
        simpa [GenContFract.IntFractPair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_ne_zero]

