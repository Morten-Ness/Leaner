import Mathlib

variable {R S : Type*}

variable (f : S → R) (hf : Function.Injective f)

variable [Add S] [Mul S]

theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib x y z := hf <| by simp only [*, right_distrib]

