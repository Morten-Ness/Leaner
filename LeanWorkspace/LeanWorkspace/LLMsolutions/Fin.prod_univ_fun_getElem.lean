FAIL
import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_fun_getElem (l : List ι) (f : ι → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  classical
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp [ih, Fin.prod_univ_succ]
