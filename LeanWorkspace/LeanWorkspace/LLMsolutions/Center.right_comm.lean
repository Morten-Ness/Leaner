FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  calc
    a * b * c = a * (b * c) := by rw [mul_assoc]
    _ = a * (c * b) := by rw [h.comm b]
    _ = a * c * b := by rw [mul_assoc]
