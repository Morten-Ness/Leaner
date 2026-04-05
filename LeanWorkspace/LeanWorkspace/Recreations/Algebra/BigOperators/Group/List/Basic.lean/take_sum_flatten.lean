import Mathlib

variable {ι α β M N P G : Type*}

theorem take_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.take ((L.map length).take i).sum = (L.take i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

