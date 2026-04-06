FAIL
import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  intro x
  simpa using (CharZero.cast_eq_zero_iff (R := R) x) <|> exact by
    rw [← Nat.modEq_zero_iff_dvd]
    simpa using (CharP.cast_eq_zero_iff (R := R) (p := ringChar R) x)
