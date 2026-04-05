import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_vecMulVec (u v : n → R) :
    (vecMulVec u v).charpoly = Polynomial.X ^ Fintype.card n - (u ⬝ᵥ v) • Polynomial.X ^ (Fintype.card n - 1) := by
  cases isEmpty_or_nonempty n
  · simp
  · have h : 1 ≤ Fintype.card n := NeZero.one_le
    rw [vecMulVec_eq (ι := Unit), Matrix.charpoly_mul_comm_of_le (n := Unit) _ _ h, Matrix.charpoly, Matrix.charmatrix]
    simp [-Matrix.map_mul, mul_sub, ← pow_succ, h, dotProduct_comm, smul_eq_C_mul]

