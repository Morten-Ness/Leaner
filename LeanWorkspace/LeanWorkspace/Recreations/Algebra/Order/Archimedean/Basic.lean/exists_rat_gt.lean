import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_rat_gt (x : K) : ∃ q : ℚ, x < q := archimedean_iff_rat_lt.mp ‹_› _

