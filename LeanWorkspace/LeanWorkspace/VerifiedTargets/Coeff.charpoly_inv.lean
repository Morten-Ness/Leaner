import Mathlib

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
