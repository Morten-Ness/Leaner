import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      v = compExactValue ((of v).contsAux n) ((of v).contsAux <| n + 1) ifp_n.fr := by
  let g := of v
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    obtain rfl : IntFractPair.of v = ifp_zero := by
      have : IntFractPair.stream v 0 = some (IntFractPair.of v) := rfl
      simpa only [this, Option.some.injEq] using stream_zero_eq
    cases eq_or_ne (Int.fract v) 0 with
    | inl fract_eq_zero =>
      -- Int.fract v = 0; we must then have `v = ⌊v⌋`
      suffices v = ⌊v⌋ by
        simpa [nextConts, nextNum, nextDen, compExactValue, IntFractPair.of, fract_eq_zero]
      calc
        v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
        _ = ⌊v⌋ := by simp [fract_eq_zero]
    | inr fract_ne_zero =>
      -- Int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
      simp [field, contsAux, nextConts, nextNum, nextDen, of_h_eq_floor, compExactValue,
        IntFractPair.of, fract_ne_zero]
  | succ n IH =>
    intro ifp_succ_n succ_nth_stream_eq
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, -⟩ :
      ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
        ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
      IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    -- introduce some notation
    let conts := g.contsAux (n + 2)
    set pconts := g.contsAux (n + 1) with pconts_eq
    set ppconts := g.contsAux n with ppconts_eq
    cases eq_or_ne ifp_succ_n.fr 0 with
    | inl ifp_succ_n_fr_eq_zero =>
      -- ifp_succ_n.fr = 0
      suffices v = conts.a / conts.b by simpa [compExactValue, ifp_succ_n_fr_eq_zero]
      -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
          ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
        IntFractPair.exists_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
      rw [← ifp_n_fract_inv_eq_floor] at s_nth_eq
      suffices v = compExactValue ppconts pconts ifp_n.fr by
        simpa [conts, contsAux, s_nth_eq, compExactValue, nth_fract_ne_zero] using this
      exact IH nth_stream_eq
    | inr ifp_succ_n_fr_ne_zero =>
      -- ifp_succ_n.fr ≠ 0
      -- use the IH to show that the following equality suffices
      suffices
        compExactValue ppconts pconts ifp_n.fr = compExactValue pconts conts ifp_succ_n.fr by grind
      -- get the correspondence between ifp_n and ifp_succ_n
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
        ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
        IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
      have : ifp_n' = ifp_n := by injection Eq.trans nth_stream_eq'.symm nth_stream_eq
      cases this
      -- get the correspondence between ifp_n and g.s.nth n
      have s_nth_eq : g.s.get? n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩ :=
        get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero
      -- the claim now follows by unfolding the definitions and tedious calculations
      -- some shorthand notation
      let ppA := ppconts.a
      let ppB := ppconts.b
      let pA := pconts.a
      let pB := pconts.b
      have : compExactValue ppconts pconts ifp_n.fr =
          (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB) := by
        -- unfold compExactValue and the convergent computation once
        simp only [compExactValue, ifp_n_fract_ne_zero, ↓reduceIte, nextConts, nextNum, one_mul,
          nextDen, ppA, ppB]
        ac_rfl
      rw [this]
      -- two calculations needed to show the claim
      have tmp_calc :=
        GenContFract.compExactValue_correctness_of_stream_eq_some_aux_comp pA ppA ifp_succ_n_fr_ne_zero
      have tmp_calc' :=
        GenContFract.compExactValue_correctness_of_stream_eq_some_aux_comp pB ppB ifp_succ_n_fr_ne_zero
      let f := Int.fract (1 / ifp_n.fr)
      -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
      dsimp only [conts, pconts, ppconts]
      have hfr : (IntFractPair.of (1 / ifp_n.fr)).fr = f := rfl
      simp [compExactValue, contsAux_recurrence s_nth_eq ppconts_eq pconts_eq,
        nextConts, nextNum, nextDen]
      grind

