import Mathlib

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charmatrix_apply_natDegree [Nontrivial R] (i j : n) :
    (Matrix.charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases h : i = j <;> simp [h]

end

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) :
    M.charpoly.degree = Fintype.card n := by
  by_cases h : Fintype.card n = 0
  · rw [h]
    unfold Matrix.charpoly
    rw [Matrix.det_eq_one_of_card_eq_zero]
    · simp
    · assumption
  rw [← sub_add_cancel M.charpoly (∏ i : n, (Polynomial.X - Polynomial.C (M i i)))]
  -- Porting note: added `↑` in front of `Fintype.card n`
  have h1 : (∏ i : n, (Polynomial.X - Polynomial.C (M i i))).degree = ↑(Fintype.card n) := by
    rw [Polynomial.degree_eq_iff_natDegree_eq_of_pos (Nat.pos_of_ne_zero h), Polynomial.natDegree_prod']
    · simp_rw [Polynomial.natDegree_X_sub_C]
      rw [← Finset.card_univ, Finset.sum_const, smul_eq_mul, mul_one]
    simp_rw [(Polynomial.monic_X_sub_C _).leadingCoeff]
    simp
  rw [Polynomial.degree_add_eq_right_of_degree_lt]
  · exact h1
  rw [h1]
  apply lt_trans (Matrix.charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

end

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_fin_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.charpoly = Polynomial.X ^ 2 - Polynomial.C M.trace * Polynomial.X + Polynomial.C M.det := M.charpoly_of_card_eq_two <| Fintype.card_fin _

end

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_inv (A : Matrix n n R) (h : IsUnit A) :
    A⁻¹.charpoly = (-1) ^ Fintype.card n * Polynomial.C A.det⁻¹ʳ * A.charpolyRev := by
  have : Invertible A := h.invertible
  calc
  _ = (Matrix.scalar n Polynomial.X - Polynomial.C.mapMatrix A⁻¹).det := rfl
  _ = Polynomial.C (A⁻¹ * A).det * (Matrix.scalar n Polynomial.X - Polynomial.C.mapMatrix A⁻¹).det := by simp
  _ = Polynomial.C A⁻¹.det * Polynomial.C A.det * (Matrix.scalar n Polynomial.X - Polynomial.C.mapMatrix A⁻¹).det := by rw [Matrix.det_mul]; simp
  _ = Polynomial.C A⁻¹.det * (Polynomial.C A.det * (Matrix.scalar n Polynomial.X - Polynomial.C.mapMatrix A⁻¹).det) := by ac_rfl
  _ = Polynomial.C A⁻¹.det * (Polynomial.C.mapMatrix A * (Matrix.scalar n Polynomial.X - Polynomial.C.mapMatrix A⁻¹)).det := by simp [RingHom.map_det]
  _ = Polynomial.C A⁻¹.det * (Polynomial.C.mapMatrix A * Matrix.scalar n Polynomial.X - 1).det := by rw [mul_sub, ← map_mul]; simp
  _ = Polynomial.C A⁻¹.det * ((-1) ^ Fintype.card n * (1 - Matrix.scalar n Polynomial.X * Polynomial.C.mapMatrix A).det) := by
    rw [← neg_sub, Matrix.det_neg, Matrix.det_one_sub_mul_comm]
  _ = _ := by simp [Matrix.charpolyRev, Matrix.smul_eq_diagonal_mul]; ac_rfl

end

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality R
  by_cases h : Fintype.card n = 0
  · rw [Matrix.charpoly, Matrix.det_eq_one_of_card_eq_zero h]
    apply Polynomial.monic_one
  have mon : (∏ i : n, (Polynomial.X - Polynomial.C (M i i))).Monic := by
    apply Polynomial.monic_prod_of_monic Finset.univ fun i : n => Polynomial.X - Polynomial.C (M i i)
    simp [Polynomial.monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, (Polynomial.X - Polynomial.C (M i i))) M.charpoly] at mon
  rw [Polynomial.Monic] at *
  rwa [Polynomial.leadingCoeff_add_of_degree_lt] at mon
  rw [Matrix.charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [Polynomial.degree_neg]
  apply lt_trans (Matrix.charpoly_sub_diagonal_degree_lt M)
  rw [Nat.cast_lt]
  lia

end

section

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

end

section

open scoped Ring

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    Matrix.trace M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [Matrix.charpoly_coeff_eq_prod_coeff_of_le _ le_rfl, Fintype.card,
    Polynomial.prod_X_sub_C_coeff_card_pred Finset.univ (fun i : n => M i i) Fintype.card_pos, neg_neg, Matrix.trace]
  simp_rw [Matrix.diag_apply]

end
