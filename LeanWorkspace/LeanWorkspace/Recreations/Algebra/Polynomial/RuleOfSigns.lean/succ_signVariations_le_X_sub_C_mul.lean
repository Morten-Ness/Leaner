import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

private theorem exists_cons_of_leadingCoeff_pos (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff ≠ 0) :
    ∃ c₀ cs, ((X - C η) * P).coeffList = P.leadingCoeff :: c₀ :: cs ∧
      ((X - C η) * P.eraseLead).coeffList = P.nextCoeff :: cs := by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) ≠ 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead ≠ 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃, natDegree_X_sub_C, add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]


set_option linter.flexible false in
theorem succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P ≠ 0) :
    Polynomial.signVariations P + 1 ≤ Polynomial.signVariations ((X - C η) * P) := by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with | _ d ih =>
  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])
  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P ≠ 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP, natDegree_X_sub_C, add_comm]
  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      simp_all [coeff_X_sub_C_mul, coeff_eq_zero_of_natDegree_lt]
    dsimp [Polynomial.signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP, withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]
  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul
  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]
  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]
  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]
    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [Polynomial.succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : Polynomial.signVariations ((X - C η) * P).eraseLead + 1 =
          Polynomial.signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          Polynomial.signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations ≤
          ((X - C η) * P).eraseLead.signVariations := by
        have := Polynomial.signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [Polynomial.signVariations_le_eraseLead_succ]
  all_goals (
    have h₁ : nextCoeff P ≠ 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [Polynomial.signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl)
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, Polynomial.signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [Polynomial.signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [Polynomial.signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]

