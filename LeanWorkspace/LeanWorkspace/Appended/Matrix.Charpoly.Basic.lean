import Mathlib

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charmatrix_map (M : Matrix n n R) (f : R →+* S) :
    Matrix.charmatrix (M.map f) = (Matrix.charmatrix M).map (Polynomial.map f) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.charmatrix, diagonal]

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

theorem charpoly_mul_comm (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly := (isRegular_X_pow _).left.eq_iff.mp <| Matrix.charpoly_mul_comm' A B

end

section

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_units_conj' (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M⁻¹.val * N * M.val).charpoly = N.charpoly := Matrix.charpoly_units_conj M⁻¹ N

set_option backward.isDefEq.respectTransparency false in

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
