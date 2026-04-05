import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem det_adjugate (A : Matrix n n α) : (Matrix.adjugate A).det = A.det ^ (Fintype.card n - 1) := by
  -- get rid of the `- 1`
  rcases (Fintype.card n).eq_zero_or_pos with h_card | h_card
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h_card
    rw [h_card, Nat.zero_sub, pow_zero, Matrix.adjugate_subsingleton, det_one]
  replace h_card := tsub_add_cancel_of_le h_card.nat_succ_le
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  suffices A'.adjugate.det = A'.det ^ (Fintype.card n - 1) by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_det, ←
      AlgHom.map_det, ← map_pow, this]
  apply mul_left_cancel₀ (show A'.det ≠ 0 from det_mvPolynomialX_ne_zero n ℤ)
  calc
    A'.det * A'.adjugate.det = (A' * Matrix.adjugate A').det := (det_mul _ _).symm
    _ = A'.det ^ Fintype.card n := by erw [Matrix.mul_adjugate A']; rw [det_smul, det_one, mul_one]
    _ = A'.det * A'.det ^ (Fintype.card n - 1) := by rw [← pow_succ', h_card]

