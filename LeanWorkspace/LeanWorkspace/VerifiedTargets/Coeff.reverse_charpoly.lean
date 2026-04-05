import Mathlib

open scoped Ring LaurentPolynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = M.charpolyRev := by
  nontriviality R
  let t : R[T;T⁻¹] := LaurentPolynomial.T 1
  let t_inv : R[T;T⁻¹] := LaurentPolynomial.T (-1)
  let p : R[T;T⁻¹] := Matrix.det (Matrix.scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := Matrix.det (1 - Matrix.scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  have hp : Polynomial.toLaurentAlg M.charpoly = p := by
    simp [p, t, Matrix.charpoly, Matrix.charmatrix, AlgHom.map_det, map_sub]
  have hq : Polynomial.toLaurentAlg M.charpolyRev = q := by
    simp [q, t, Matrix.charpolyRev, AlgHom.map_det, map_sub, Matrix.smul_eq_diagonal_mul]
  suffices t_inv ^ Fintype.card n * p = LaurentPolynomial.invert q by
    apply Polynomial.toLaurent_injective
    rwa [LaurentPolynomial.toLaurent_reverse, ← Polynomial.coe_toLaurentAlg, hp, hq, ← LaurentPolynomial.involutive_invert.injective.eq_iff,
      map_mul, LaurentPolynomial.involutive_invert p, Matrix.charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← LaurentPolynomial.T_pow, map_pow, LaurentPolynomial.invert_T, mul_comm]
  rw [← Matrix.det_smul, smul_sub, Matrix.scalar_apply, ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul, ht,
    Matrix.diagonal_one, LaurentPolynomial.invert.map_det]
  simp [t_inv, map_sub, map_one, map_mul, t, Matrix.smul_eq_diagonal_mul]

