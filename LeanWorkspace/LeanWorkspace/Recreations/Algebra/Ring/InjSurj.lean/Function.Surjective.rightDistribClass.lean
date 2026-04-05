import Mathlib

variable {R S : Type*}

variable (f : R → S) (hf : Function.Surjective f)

variable [Add S] [Mul S]

theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

