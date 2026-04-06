FAIL
import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.prod_univ_succ, List.finRange_succ]
      simp [ih, Function.comp]
