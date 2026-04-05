import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
    IsLieAbelian (LieAlgebra.derivedSeriesOfIdeal R L k I) ↔ LieAlgebra.derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm, LieAlgebra.derivedSeriesOfIdeal_add I 1 k, LieAlgebra.abelian_iff_derived_one_eq_bot]

