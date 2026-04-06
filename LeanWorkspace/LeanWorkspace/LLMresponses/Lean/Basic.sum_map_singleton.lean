FAIL
import Mathlib

variable {F ι κ G M N O : Type*}

theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s := by
  refine Quot.inductionOn s ?_
  intro l
  induction l with
  | nil =>
      rfl
  | cons a t ih =>
      simp [ih]
