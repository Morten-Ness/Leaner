import Mathlib

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

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


theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) ≤ Polynomial.signVariations P := by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P --Induct on number of roots.
  · exact zero_le _
  rename_i ih
  have hp : P ≠ 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : ∃ x, x ∈ P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, Polynomial.succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

