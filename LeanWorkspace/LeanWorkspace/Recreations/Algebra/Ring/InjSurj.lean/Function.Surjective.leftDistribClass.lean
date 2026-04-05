import Mathlib

variable {R S : Type*}

variable (f : R → S) (hf : Function.Surjective f)

variable [Add S] [Mul S]

theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

