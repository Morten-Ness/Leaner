import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_eq_sum : f.smeval x = Finsupp.sum f fun n r => r • (x ^ n).val := rfl

