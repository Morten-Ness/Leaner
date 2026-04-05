import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

theorem derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : ℕ) :
    D (k + l) (I + J) ≤ D k I + D l J := by
  let D₁ : LieIdeal R L →o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : ∀ I J : LieIdeal R L, D₁ (I ⊔ J) ≤ D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [← D₁.iterate_sup_le_sup_iff] at h₁
  exact h₁ k l I J

