import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  calc
    (x + y) * (x + y) = x * x + x * y + (y * x + y * y) := by
      simp [add_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
        mul_assoc]
    _ = x * x + y * y := by
      rw [mul_comm y x]
      have h2 : (2 : R) = 0 := by simpa using (CharP.cast_eq_zero (R := R) 2)
      calc
        x * x + x * y + (x * y + y * y) = x * x + ((2 : R) * (x * y)) + y * y := by
          rw [two_mul]
          simp [add_assoc, add_left_comm, add_comm]
        _ = x * x + 0 + y * y := by rw [h2, zero_mul]
        _ = x * x + y * y := by simp
