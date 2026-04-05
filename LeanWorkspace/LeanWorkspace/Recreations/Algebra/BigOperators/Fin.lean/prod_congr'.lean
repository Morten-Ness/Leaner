import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_congr' {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (i.cast h)) = ∏ i : Fin b, f i := by
  subst h
  congr

