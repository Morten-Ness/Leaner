FAIL
import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem CharOne.subsingleton [CharP R 1] : Subsingleton R := by
  have h01 : (0 : R) = 1 := by
    have h10 : (1 : R) = 0 := by
      simpa using (CharP.cast_eq_zero (R := R) (p := 1) : ((1 : ℕ) : R) = 0)
    exact h10.symm
  refine ⟨fun a b => ?_⟩
  have ha0 : a = 0 := by
    calc
      a = a * 1 := by rw [mul_one]
      _ = a * 0 := by rw [h01]
      _ = 0 := by rw [mul_zero]
  have hb0 : b = 0 := by
    calc
      b = b * 1 := by rw [mul_one]
      _ = b * 0 := by rw [h01]
      _ = 0 := by rw [mul_zero]
  rw [ha0, hb0]
