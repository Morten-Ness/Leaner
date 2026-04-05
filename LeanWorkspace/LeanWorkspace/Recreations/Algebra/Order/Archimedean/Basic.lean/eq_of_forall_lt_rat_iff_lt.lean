import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y := (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

