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


theorem signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff) :
    Polynomial.signVariations ((X - C η) * P.eraseLead) ≤ Polynomial.signVariations ((X - C η) * P) := by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, Polynomial.signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x ↦ decide (x ≠ 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

-- TODO: fix non-terminal simp below; simp followed by rfl

