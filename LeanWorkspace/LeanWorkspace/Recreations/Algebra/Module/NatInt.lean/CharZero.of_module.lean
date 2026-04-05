import Mathlib

variable {R S M M₂ : Type*}

theorem CharZero.of_module [Semiring R] [AddCommMonoidWithOne M] [CharZero M] [Module R M] :
    CharZero R := by
  refine ⟨fun m n h => @Nat.cast_injective M _ _ _ _ ?_⟩
  rw [← nsmul_one, ← nsmul_one, ← Nat.cast_smul_eq_nsmul R, ← Nat.cast_smul_eq_nsmul R, h]

