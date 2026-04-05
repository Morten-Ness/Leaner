import Mathlib

variable {m n α β : Type*}

variable [CommSemiring α] [StarRing α] [Fintype n] [DecidableEq n]

omit [StarRing α] in
theorem Matrix.toLin'_hadamard (x y : Matrix m n α) :
    (x ⊙ y).toLin' = (toConv x.toLin' * toConv y.toLin').ofConv := by ext; simp

