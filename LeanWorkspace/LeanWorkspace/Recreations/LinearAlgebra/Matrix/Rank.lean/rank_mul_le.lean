import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_mul_le (A : Matrix m n R) (B : Matrix n o R) :
    (A * B).rank ≤ min A.rank B.rank := le_min (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)

