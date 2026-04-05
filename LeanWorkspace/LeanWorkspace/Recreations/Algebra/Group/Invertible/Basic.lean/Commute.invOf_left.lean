import Mathlib

variable {α : Type u}

theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟b) a := calc
    ⅟b * a = ⅟b * (a * b * ⅟b) := by simp [mul_assoc]
    _ = ⅟b * (b * a * ⅟b) := by rw [h.eq]
    _ = a * ⅟b := by simp [mul_assoc]

