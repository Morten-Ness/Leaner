import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ LieAlgebra.derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_zero,
    LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

