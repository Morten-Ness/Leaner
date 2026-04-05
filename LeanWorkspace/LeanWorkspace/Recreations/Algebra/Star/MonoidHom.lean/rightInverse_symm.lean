import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem rightInverse_symm (e : A ≃⋆* B) : Function.RightInverse e.symm e := e.right_inv

