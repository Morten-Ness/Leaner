import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    Polynomial.X ^ Fintype.card n * (A * B).charpoly = Polynomial.X ^ Fintype.card m * (B * A).charpoly := by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (Matrix.scalar m Polynomial.X) (A.map Polynomial.C) (B.map Polynomial.C) (1 : Matrix n n R[Polynomial.X])
  let N := fromBlocks (-1 : Matrix m m R[Polynomial.X]) 0 (B.map Polynomial.C) (-Matrix.scalar n Polynomial.X)
  have hMN :
      M * N = fromBlocks (-Matrix.scalar m Polynomial.X + (A * B).map Polynomial.C) (-(Polynomial.X : R[Polynomial.X]) • A.map Polynomial.C) 0 (-Matrix.scalar n Polynomial.X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-Matrix.scalar m Polynomial.X) (-A.map Polynomial.C) 0 ((B * A).map Polynomial.C - Matrix.scalar n Polynomial.X) := by
    simp [M, N, fromBlocks_multiply, sub_eq_add_neg, -scalar_apply, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[Polynomial.X]) ^ (Fintype.card m + Fintype.card n) *
      (Polynomial.X ^ Fintype.card n * (Matrix.scalar m Polynomial.X - (A * B).map Polynomial.C).det) := by
    rw [hMN, det_fromBlocks_zero₂₁, neg_add_eq_sub, ← neg_sub, Matrix.det_neg]
    simp
    ring
  have hdet_NM : (N * M).det = (-1 : R[Polynomial.X]) ^ (Fintype.card m + Fintype.card n) *
      (Polynomial.X ^ Fintype.card m * (Matrix.scalar n Polynomial.X - (B * A).map Polynomial.C).det) := by
    rw [hNM, det_fromBlocks_zero₂₁, ← neg_sub, Matrix.det_neg (_ - _)]
    simp
    ring
  dsimp only [Matrix.charpoly, Matrix.charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff, ← hdet_NM, ← hdet_MN, det_mul_comm]

