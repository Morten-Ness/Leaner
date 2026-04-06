FAIL
import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      rw [List.length_cons, Fin.prod_univ_succ]
      simp [ih, List.prod_cons]
