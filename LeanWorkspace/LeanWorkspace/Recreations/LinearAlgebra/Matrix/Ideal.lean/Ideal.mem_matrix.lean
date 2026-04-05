import Mathlib

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

theorem mem_matrix (I : Ideal R) (M : Matrix n n R) :
    M ∈ I.matrix n ↔ ∀ i j, M i j ∈ I := by rfl

