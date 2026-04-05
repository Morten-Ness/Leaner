import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_mul_comm' (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly := by
  -- This proof follows https://math.stackexchange.com/a/311362/315369
  let M := fromBlocks (scalar m X) (A.map C) (B.map C) (1 : Matrix n n R[X])
  let N := fromBlocks (-1 : Matrix m m R[X]) 0 (B.map C) (-scalar n X)
  have hMN :
      M * N = fromBlocks (-scalar m X + (A * B).map C) (-(X : R[X]) • A.map C) 0 (-scalar n X) := by
    simp [M, N, fromBlocks_multiply, smul_eq_mul_diagonal, -diagonal_neg]
  have hNM : N * M = fromBlocks (-scalar m X) (-A.map C) 0 ((B * A).map C - scalar n X) := by
    simp [M, N, fromBlocks_multiply, sub_eq_add_neg, -scalar_apply, scalar_comm, Commute.all]
  have hdet_MN : (M * N).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card n * (scalar m X - (A * B).map C).det) := by
    rw [hMN, det_fromBlocks_zero₂₁, neg_add_eq_sub, ← neg_sub, det_neg]
    simp
    ring
  have hdet_NM : (N * M).det = (-1 : R[X]) ^ (Fintype.card m + Fintype.card n) *
      (X ^ Fintype.card m * (scalar n X - (B * A).map C).det) := by
    rw [hNM, det_fromBlocks_zero₂₁, ← neg_sub, det_neg (_ - _)]
    simp
    ring
  dsimp only [Matrix.charpoly, Matrix.charmatrix, RingHom.mapMatrix_apply]
  rw [← (isUnit_neg_one.pow _).isRegular.left.eq_iff, ← hdet_NM, ← hdet_MN, det_mul_comm]

