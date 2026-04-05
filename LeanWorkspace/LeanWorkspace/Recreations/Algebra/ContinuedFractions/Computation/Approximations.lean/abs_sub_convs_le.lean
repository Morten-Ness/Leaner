import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n * ((of v).dens <| n + 1)) := by
  -- shorthand notation
  let g := of v
  let nextConts := g.contsAux (n + 2)
  set conts := contsAux g (n + 1) with conts_eq
  set pred_conts := contsAux g n with pred_conts_eq
  -- change the goal to something more readable
  change |v - convs g n| ≤ 1 / (conts.b * nextConts.b)
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 not_terminatedAt_n
  have gp_a_eq_one : gp.a = 1 := GenContFract.of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  -- unfold the recurrence relation for `nextConts.b`
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [nextConts, contsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  let den := conts.b * (pred_conts.b + gp.b * conts.b)
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      ∃ ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    ∃ ifp_n, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
      ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  let den' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b)
  -- now we can use `GenContFract.sub_convs_eq` to simplify our goal
  suffices |(-1) ^ n / den'| ≤ 1 / den by grind [GenContFract.sub_convs_eq]
  -- derive some tedious inequalities that we need to rewrite our goal
  have nextConts_b_ineq : (fib (n + 2) : K) ≤ pred_conts.b + gp.b * conts.b := by
    have : (fib (n + 2) : K) ≤ nextConts.b :=
      GenContFract.fib_le_of_contsAux_b (Or.inr not_terminatedAt_n)
    rwa [nextConts_b_eq] at this
  have conts_b_ineq : (fib (n + 1) : K) ≤ conts.b :=
    haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
    GenContFract.fib_le_of_contsAux_b <| Or.inr this
  have zero_lt_conts_b : 0 < conts.b :=
    conts_b_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
  -- `den'` is positive, so we can remove `|⬝|` from our goal
  suffices 1 / den' ≤ 1 / den by
    have : |(-1) ^ n / den'| = 1 / den' := by
      suffices 1 / |den'| = 1 / den' by rwa [abs_div, abs_neg_one_pow n]
      have : 0 < den' := by
        have : 0 ≤ pred_conts.b :=
          haveI : (fib n : K) ≤ pred_conts.b :=
            haveI : ¬g.TerminatedAt (n - 2) :=
              mt (terminated_stable (n.sub_le 2)) not_terminatedAt_n
            GenContFract.fib_le_of_contsAux_b <| Or.inr this
          le_trans (mod_cast (fib n).zero_le) this
        have : 0 < ifp_n.fr⁻¹ :=
          haveI zero_le_ifp_n_fract : 0 ≤ ifp_n.fr :=
            IntFractPair.nth_stream_fr_nonneg stream_nth_eq
          inv_pos.2 (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)
        positivity
      rw [abs_of_pos this]
    rwa [this]
  suffices 0 < den ∧ den ≤ den' from div_le_div_of_nonneg_left zero_le_one this.1 this.2
  constructor
  · have : 0 < pred_conts.b + gp.b * conts.b :=
      nextConts_b_ineq.trans_lt' <| mod_cast fib_pos.2 <| succ_pos _
    solve_by_elim [mul_pos]
  · -- we can cancel multiplication by `conts.b` and addition with `pred_conts.b`
    suffices gp.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b by
      simp only [den, den']; gcongr
    suffices (ifp_succ_n.b : K) * conts.b ≤ ifp_n.fr⁻¹ * conts.b by rwa [← ifp_succ_n_b_eq_gp_b]
    have : (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ :=
      IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq
    gcongr

