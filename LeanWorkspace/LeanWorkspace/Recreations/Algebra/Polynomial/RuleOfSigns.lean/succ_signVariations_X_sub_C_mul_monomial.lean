import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

theorem succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c ≠ 0) (hη : 0 < η) :
    (monomial d c).signVariations + 1 ≤ ((X - C η) * monomial d c).signVariations := by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c using 1
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) ≠ 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c ≠ SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', Polynomial.signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

