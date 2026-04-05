import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_mul_le_left (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ A.rank := by
  nontriviality R
  rw [Matrix.rank, Matrix.rank, mulVecLin_mul]
  exact Cardinal.toNat_le_toNat (LinearMap.rank_comp_le_left _ _) (rank_lt_aleph0 _ _)

