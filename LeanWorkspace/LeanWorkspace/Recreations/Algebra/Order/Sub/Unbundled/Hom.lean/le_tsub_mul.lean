import Mathlib

variable {α β : Type*}

variable [Preorder α] [Add α] [Sub α] [OrderedSub α]

theorem le_tsub_mul {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub

