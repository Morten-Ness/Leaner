import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_rat_mem_uIoo {x y : K} (h : x ≠ y) : ∃ q : ℚ, ↑q ∈ Set.uIoo x y := exists_rat_btwn (min_lt_max.mpr h)

