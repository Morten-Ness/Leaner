import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeriesOfIdeal_add (k l : ℕ) : D (k + l) I = D k (D l I) := by
  induction k with
  | zero => rw [Nat.zero_add, LieAlgebra.derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_succ, ih]

