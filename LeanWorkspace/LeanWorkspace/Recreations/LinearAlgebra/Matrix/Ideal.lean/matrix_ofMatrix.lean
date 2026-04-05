import Mathlib

variable {R n : Type*}

variable [NonAssocSemiring R] [Fintype n]

theorem matrix_ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) :
    RingCon.matrix n (RingCon.ofMatrix c) = c := by
  ext x y
  classical
  constructor
  · intro h
    rw [matrix_eq_sum_single x, matrix_eq_sum_single y]
    refine c.finset_sum _ fun i _ ↦ c.finset_sum _ fun j _ ↦ h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

