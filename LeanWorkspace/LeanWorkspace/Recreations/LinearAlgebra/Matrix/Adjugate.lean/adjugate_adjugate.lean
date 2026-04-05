import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_adjugate (A : Matrix n n α) (h : Fintype.card n ≠ 1) :
    Matrix.adjugate (Matrix.adjugate A) = det A ^ (Fintype.card n - 2) • A := by
  -- get rid of the `- 2`
  rcases h_card : Fintype.card n with _ | n'
  · subsingleton [Fintype.card_eq_zero_iff.mp h_card]
  cases n'
  · exact (h h_card).elim
  rw [← h_card]
  -- express `A` as an evaluation of a polynomial in n^2 variables, and solve in the polynomial ring
  -- where `A'.det` is non-zero.
  let A' := mvPolynomialX n n ℤ
  suffices Matrix.adjugate (Matrix.adjugate A') = det A' ^ (Fintype.card n - 2) • A' by
    rw [← mvPolynomialX_mapMatrix_aeval ℤ A, ← AlgHom.map_adjugate, ← AlgHom.map_adjugate, this,
      ← AlgHom.map_det, ← map_pow (MvPolynomial.aeval fun p : n × n ↦ A p.1 p.2),
      AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _)]
  have h_card' : Fintype.card n - 2 + 1 = Fintype.card n - 1 := by simp [h_card]
  have is_reg : IsSMulRegular (MvPolynomial (n × n) ℤ) (det A') := fun x y =>
    mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ)
  apply is_reg.matrix
  simp only
  rw [smul_smul, ← pow_succ', h_card', Matrix.det_smul_adjugate_adjugate]

