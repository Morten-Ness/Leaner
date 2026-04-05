import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeriesOfIdeal_succ_le (k : ℕ) : D (k + 1) I ≤ D k I := LieAlgebra.derivedSeriesOfIdeal_le (le_refl I) k.le_succ

