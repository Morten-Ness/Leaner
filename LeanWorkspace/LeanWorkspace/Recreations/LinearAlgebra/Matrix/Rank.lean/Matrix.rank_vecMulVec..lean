import Mathlib

set_option backward.isDefEq.respectTransparency false in
theorem Matrix.rank_vecMulVec.{u} {K m n : Type u} [CommRing K] [Fintype n]
    [DecidableEq n] (w : m → K) (v : n → K) : (Matrix.vecMulVec w v).toLin'.rank ≤ 1 := by
  nontriviality K
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.toLin'_mul]
  refine le_trans (LinearMap.rank_comp_le_left _ _) ?_
  refine (LinearMap.rank_le_domain _).trans_eq ?_
  rw [rank_fun', Fintype.card_ofSubsingleton, Nat.cast_one]

