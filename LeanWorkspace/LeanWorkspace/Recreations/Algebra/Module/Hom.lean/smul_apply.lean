import Mathlib

variable {R S M A B : Type*}

variable [Monoid R] [Monoid S] [AddCommMonoid A]

variable [DistribMulAction R A] [DistribMulAction S A]

theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x := rfl

