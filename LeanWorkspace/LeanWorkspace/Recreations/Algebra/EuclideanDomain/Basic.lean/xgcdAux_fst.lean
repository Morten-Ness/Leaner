import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcdAux_fst (x y : R) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y := GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left, gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, IH]
    rw [← EuclideanDomain.gcd_val]

