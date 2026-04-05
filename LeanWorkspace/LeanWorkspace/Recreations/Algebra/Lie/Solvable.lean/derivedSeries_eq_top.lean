import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeries_eq_top (n : ℕ) (h : derivedSeries R L 1 = ⊤) :
    derivedSeries R L n = ⊤ := by
  cases n
  · rfl
  · rwa [LieIdeal.derivedSeries_succ_eq_top_iff]

