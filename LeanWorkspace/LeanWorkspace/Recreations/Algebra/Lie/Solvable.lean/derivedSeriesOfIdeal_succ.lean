import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeriesOfIdeal_succ (k : ℕ) :
    LieAlgebra.derivedSeriesOfIdeal R L (k + 1) I =
      ⁅LieAlgebra.derivedSeriesOfIdeal R L k I, LieAlgebra.derivedSeriesOfIdeal R L k I⁆ := Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

