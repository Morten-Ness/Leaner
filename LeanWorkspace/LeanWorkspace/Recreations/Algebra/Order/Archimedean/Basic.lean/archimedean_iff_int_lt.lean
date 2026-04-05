import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_int_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x < n := ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

