import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_permute_cols (σ : Equiv.Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).permanent = M.permanent := (Group.mulLeft_bijective σ).sum_comp fun τ ↦ ∏ i : n, M (τ i) i

