import Mathlib

variable {ι α β M N P G : Type*}

theorem sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp [List.sum_cons, ih, Int.add_emod]
