import Mathlib

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem reverse_charpoly (M : Matrix n n R) :
    M.charpoly.reverse = M.charpolyRev := by
  nontriviality R
  let t : R[T;T⁻¹] := T 1
  let t_inv : R[T;T⁻¹] := T (-1)
  let p : R[T;T⁻¹] := det (scalar n t - M.map LaurentPolynomial.C)
  let q : R[T;T⁻¹] := det (1 - scalar n t * M.map LaurentPolynomial.C)
  have ht : t_inv * t = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  have hp : toLaurentAlg M.charpoly = p := by
    simp [p, t, charpoly, charmatrix, AlgHom.map_det, map_sub]
  have hq : toLaurentAlg M.charpolyRev = q := by
    simp [q, t, Matrix.charpolyRev, AlgHom.map_det, map_sub, smul_eq_diagonal_mul]
  suffices t_inv ^ Fintype.card n * p = invert q by
    apply toLaurent_injective
    rwa [toLaurent_reverse, ← coe_toLaurentAlg, hp, hq, ← involutive_invert.injective.eq_iff,
      map_mul, involutive_invert p, charpoly_natDegree_eq_dim,
      ← mul_one (Fintype.card n : ℤ), ← T_pow, map_pow, invert_T, mul_comm]
  rw [← det_smul, smul_sub, scalar_apply, ← diagonal_smul, Pi.smul_def, smul_eq_mul, ht,
    diagonal_one, invert.map_det]
  simp [t_inv, map_sub, map_one, map_mul, t, smul_eq_diagonal_mul]

