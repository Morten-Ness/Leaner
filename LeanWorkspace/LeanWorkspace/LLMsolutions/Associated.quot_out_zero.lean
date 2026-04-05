import Mathlib

variable {M : Type*}

variable [MonoidWithZero M]

theorem quot_out_zero : Quot.out (0 : Associates M) = 0 := by
  let x : M := Quot.out (0 : Associates M)
  have h : Associated x 0 := Quotient.exact (Quotient.out_eq (0 : Associates M))
  simpa [x] using h.eq_zero_iff.mp rfl
