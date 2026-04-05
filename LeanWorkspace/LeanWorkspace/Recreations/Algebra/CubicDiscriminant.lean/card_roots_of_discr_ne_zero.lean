import Mathlib

variable {R S F K : Type*}

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]


private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [(Cubic.toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩


theorem card_roots_of_discr_ne_zero [DecidableEq K] (ha : P.a ≠ 0) (h3 : (P.toPoly.map φ).Splits)
    (hd : P.discr ≠ 0) : (Cubic.map φ P).roots.toFinset.card = 3 := by
  rwa [toFinset_card_of_nodup <| (Cubic.discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← Cubic.splits_iff_card_roots ha]

