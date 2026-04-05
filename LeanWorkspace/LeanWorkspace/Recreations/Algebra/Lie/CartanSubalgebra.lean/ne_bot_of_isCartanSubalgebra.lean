import Mathlib

variable {R : Type u} {L : Type v}

variable [CommRing R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

theorem ne_bot_of_isCartanSubalgebra [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H ≠ ⊥ := by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x ∈ H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)

