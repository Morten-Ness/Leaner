import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem ext ⦃f g : AbsoluteValue R S⦄ : (∀ x, f x = g x) → f = g := DFunLike.ext _ _

