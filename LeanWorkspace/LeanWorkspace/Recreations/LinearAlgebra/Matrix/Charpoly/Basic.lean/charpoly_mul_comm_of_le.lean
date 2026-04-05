import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_mul_comm_of_le
    (A : Matrix m n R) (B : Matrix n m R) (hle : Fintype.card n ≤ Fintype.card m) :
    (A * B).charpoly = X ^ (Fintype.card m - Fintype.card n) * (B * A).charpoly := by
  rw [← (isRegular_X_pow _).left.eq_iff, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hle, Matrix.charpoly_mul_comm']

