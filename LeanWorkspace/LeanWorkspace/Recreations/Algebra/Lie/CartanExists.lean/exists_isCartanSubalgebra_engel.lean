import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

theorem exists_isCartanSubalgebra_engel [Infinite K] :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  apply LieAlgebra.exists_isCartanSubalgebra_engel_of_finrank_le_card
  exact natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

