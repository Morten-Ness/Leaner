import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_rat_lt : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x < q where
  mp _ x := let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x ↦
    let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h <| mod_cast Nat.le_ceil _⟩

