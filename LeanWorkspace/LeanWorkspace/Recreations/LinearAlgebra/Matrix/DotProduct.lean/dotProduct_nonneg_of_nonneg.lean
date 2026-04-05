import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

theorem dotProduct_nonneg_of_nonneg {v w : n → R} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w := Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

