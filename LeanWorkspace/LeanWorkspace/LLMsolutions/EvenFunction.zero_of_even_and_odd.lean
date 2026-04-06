FAIL
import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext x
  have h1 : f x = f (-x) := he x
  have h2 : f (-x) = -f x := ho x
  have h : f x = -f x := h1.trans h2
  have hsum : f x + f x = 0 := by
    calc
      f x + f x = (-f x) + f x := by rw [h]
      _ = 0 := neg_add_cancel (f x)
  have htwo : (2 : ℕ) • f x = 0 := by
    simpa [two_nsmul] using hsum
  exact eq_of_two_nsmul_zero htwo
