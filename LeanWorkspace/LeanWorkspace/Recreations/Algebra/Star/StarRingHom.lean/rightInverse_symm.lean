import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e := e.right_inv

