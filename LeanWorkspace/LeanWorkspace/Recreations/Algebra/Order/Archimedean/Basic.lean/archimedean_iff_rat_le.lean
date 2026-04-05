import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_rat_le : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x ≤ q := archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

