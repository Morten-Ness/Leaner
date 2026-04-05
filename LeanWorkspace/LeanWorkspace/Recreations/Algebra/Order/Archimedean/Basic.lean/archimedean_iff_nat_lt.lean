import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_nat_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x < n := ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

