import Mathlib

section

open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem aeval_self_charpoly (M : Matrix n n R) : Polynomial.aeval M M.charpoly = 0 := by
  -- We begin with the fact $χ_M(t) I = Matrix.adjugate (t I - M) * (t I - M)$,
  -- as an identity in `Matrix n n R[X]`.
  have h : M.charpoly • (1 : Matrix n n R[X]) = Matrix.adjugate (Matrix.charmatrix M) * Matrix.charmatrix M :=
    (Matrix.adjugate_mul _).symm
  -- Using the algebra isomorphism `Matrix n n R[X] ≃ₐ[R] Polynomial (Matrix n n R)`,
  -- we have the same identity in `Polynomial (Matrix n n R)`.
  apply_fun matPolyEquiv at h
  simp only [map_mul, Matrix.matPolyEquiv_charmatrix] at h
  -- Because the coefficient ring `Matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients, so everything telescopes.
  apply_fun fun p => p.eval M at h
  rw [Polynomial.eval_mul_X_sub_C] at h
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  rw [matPolyEquiv_smul_one, Polynomial.eval_map] at h
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  exact h

end

section

open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_apply_eq : Matrix.charmatrix M i i = (Polynomial.X : R[X]) - Polynomial.C (M i i) := by
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.map_apply,
    Matrix.diagonal_apply_eq]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_apply_ne (h : i ≠ j) : Matrix.charmatrix M i j = -Polynomial.C (M i j) := by
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h,
    Matrix.map_apply, sub_eq_neg_self]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_diagonal (d : n → R) :
    Matrix.charmatrix (Matrix.diagonal d) = Matrix.diagonal fun i => Polynomial.X - Polynomial.C (d i) := by
  rw [Matrix.charmatrix, Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_sub]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_fromBlocks :
    Matrix.charmatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (Matrix.charmatrix M₁₁) (- M₁₂.map Polynomial.C) (- M₂₁.map Polynomial.C) (Matrix.charmatrix M₂₂) := by
  simp only [Matrix.charmatrix]
  ext (i | i) (j | j) : 2 <;> simp [Matrix.diagonal]

-- TODO: importing block triangular here is somewhat expensive, if more lemmas about it are added
-- to this file, it may be worth extracting things out to Charpoly/Block.lean

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    Matrix.charmatrix (M.map f) = (Matrix.charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.charmatrix, Matrix.diagonal]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_reindex (e : n ≃ m) :
    Matrix.charmatrix (Matrix.reindex e e M) = Matrix.reindex e e (Matrix.charmatrix M) := by
  ext i j x
  by_cases h : i = j
  all_goals simp [h]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_map (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpoly = M.charpoly.map f := by
  rw [Matrix.charpoly, Matrix.charmatrix_map, ← Polynomial.coe_mapRingHom, Matrix.charpoly, RingHom.map_det,
    RingHom.mapMatrix_apply]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_reindex (e : n ≃ m)
    (M : Matrix n n R) : (Matrix.reindex e e M).charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [Matrix.charmatrix_reindex, Matrix.det_reindex_self]

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

set_option backward.isDefEq.respectTransparency false in
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - Matrix.scalar n μ).charpoly = M.charpoly.comp (Polynomial.X + Polynomial.C μ) := by
  simp_rw [Matrix.charpoly, Matrix.det_apply, Polynomial.sum_comp, Polynomial.smul_comp, Polynomial.prod_comp]
  congr! with σ _ i _
  by_cases hi : σ i = i <;> simp [hi]
  ring

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem eval_charpoly (M : Matrix m m R) (t : R) :
    M.charpoly.eval t = (Matrix.scalar _ t - M).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

end
