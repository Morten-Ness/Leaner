import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [Fintype m] [Field R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem rank_conjTranspose (A : Matrix m n R) : Aᴴ.rank = A.rank := le_antisymm
    (((Matrix.rank_conjTranspose_mul_self _).symm.trans_le <| Matrix.rank_mul_le_left _ _).trans_eq <|
      congr_arg _ <| conjTranspose_conjTranspose _)
    ((Matrix.rank_conjTranspose_mul_self _).symm.trans_le <| Matrix.rank_mul_le_left _ _)

