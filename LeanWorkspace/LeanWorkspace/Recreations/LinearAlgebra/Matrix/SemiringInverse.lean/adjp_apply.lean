import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem adjp_apply (i j : n) :
    Matrix.adjp s A i j = ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k) := rfl

