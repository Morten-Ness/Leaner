import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_vecMulVec_le (w : m → R) (v : n → R) : (Matrix.vecMulVec w v).rank ≤ 1 := by
  rw [Matrix.vecMulVec_eq Unit]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  nontriviality R
  exact Matrix.rank_le_card_width _

