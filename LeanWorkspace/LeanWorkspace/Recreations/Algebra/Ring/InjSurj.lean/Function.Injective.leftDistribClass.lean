import Mathlib

variable {R S : Type*}

variable (f : S → R) (hf : Function.Injective f)

variable [Add S] [Mul S]

theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib x y z := hf <| by simp only [*, left_distrib]

