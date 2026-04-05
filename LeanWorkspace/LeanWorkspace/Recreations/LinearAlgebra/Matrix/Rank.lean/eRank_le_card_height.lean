import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem eRank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.eRank ≤ ENat.card m := by
  classical
  wlog hfin : Finite m
  · simp [ENat.card_eq_top.2 (by simpa using hfin)]
  have _ := Fintype.ofFinite m
  rw [ENat.card_eq_coe_fintype_card, Matrix.eRank, toENat_le_natCast]
  exact A.cRank_le_card_height

