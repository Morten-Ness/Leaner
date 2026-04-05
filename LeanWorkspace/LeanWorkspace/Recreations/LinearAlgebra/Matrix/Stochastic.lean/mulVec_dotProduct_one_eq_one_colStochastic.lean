import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

variable {x : n → R}

theorem mulVec_dotProduct_one_eq_one_colStochastic (hM : M ∈ Matrix.colStochastic R n)
    (hx : 1 ⬝ᵥ x = 1) : 1 ⬝ᵥ (M *ᵥ x) = 1 := by
  rw [dotProduct_mulVec, hM.2, hx]

