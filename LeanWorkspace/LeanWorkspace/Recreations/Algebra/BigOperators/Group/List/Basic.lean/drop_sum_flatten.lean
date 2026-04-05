import Mathlib

variable {ι α β M N P G : Type*}

theorem drop_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

