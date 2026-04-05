import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_rat_lt (x : K) : ∃ q : ℚ, (q : K) < x := let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

