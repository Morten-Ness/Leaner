import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p) ≠ 0 := by
  classical
  haveI : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne, ← IsRoot, ← Polynomial.dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq, ← mul_assoc, ← pow_succ, Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp] at this
  exact
    (Polynomial.finiteMultiplicity_of_degree_pos_of_monic
      (show (0 : WithBot ℕ) < degree (Polynomial.X - Polynomial.C a) by rw [degree_X_sub_C]; decide)
      (Polynomial.monic_X_sub_C _) hp).not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)

