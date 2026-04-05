import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e := e.left_inv

