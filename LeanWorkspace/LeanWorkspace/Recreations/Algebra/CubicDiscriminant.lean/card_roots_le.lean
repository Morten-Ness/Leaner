import Mathlib

variable {R S F K : Type*}

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R →+* S}

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]


private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [(Cubic.toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩


theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · exact (card_roots' P.toPoly).trans (by rw [hP, natDegree_zero]; exact zero_le 3)
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

