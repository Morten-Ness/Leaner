import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem leftInverse_symm (e : A ≃⋆* B) : Function.LeftInverse e.symm e := e.left_inv

