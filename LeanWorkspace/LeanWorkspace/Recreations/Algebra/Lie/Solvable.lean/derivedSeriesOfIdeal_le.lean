import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : ℕ} (h₁ : I ≤ J) (h₂ : l ≤ k) :
    D k I ≤ D l J := by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, LieAlgebra.derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l ≤ k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, LieAlgebra.derivedSeriesOfIdeal_succ, LieAlgebra.derivedSeriesOfIdeal_succ]
      exact LieSubmodule.mono_lie (ih (le_refl k)) (ih (le_refl k))
    · rw [LieAlgebra.derivedSeriesOfIdeal_succ]; exact le_trans (LieSubmodule.lie_le_left _ _) (ih h)

