import Mathlib

variable {α : Type u}

theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟b) := calc
    a * ⅟b = ⅟b * (b * a * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (a * b * ⅟b) := by rw [h.eq]
    _ = ⅟b * a := by simp [mul_assoc]

