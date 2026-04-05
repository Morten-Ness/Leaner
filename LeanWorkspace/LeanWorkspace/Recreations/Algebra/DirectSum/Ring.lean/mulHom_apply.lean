import Mathlib

open scoped DirectSum

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

theorem mulHom_apply (a b : ⨁ i, A i) : DirectSum.mulHom A a b = a * b := rfl

