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


theorem splits_iff_card_roots (ha : P.a ≠ 0) :
    Splits (P.toPoly.map φ) ↔ (Cubic.map φ P).roots.card = 3 := by
  replace ha : (Cubic.map φ P).a ≠ 0 := (map_ne_zero φ).mpr ha
  rw [Cubic.roots, ← Cubic.map_toPoly, Polynomial.splits_iff_card_roots,
    ← ((degree_eq_iff_natDegree_eq <| Cubic.ne_zero_of_a_ne_zero ha).1 <| Cubic.degree_of_a_ne_zero ha : _ = 3)]

