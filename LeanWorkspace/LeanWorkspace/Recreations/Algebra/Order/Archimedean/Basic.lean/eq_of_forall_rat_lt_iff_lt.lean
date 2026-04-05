import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : K) < x ↔ (q : K) < y) : x = y := (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

