import Mathlib

variable {R S M N : Type*}

variable (R M) [Semiring R] [AddCommGroup M] [Module R M]

theorem CharZero.of_isAddTorsionFree [Nontrivial M] [IsAddTorsionFree M] : CharZero R := by
  refine ⟨fun {n m h} ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : ℤ) • x = (m : ℤ) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective ℤ hx h

