import Mathlib

variable {R H : Type*}

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

theorem mulOpposite_repr_op (b : Module.Basis ι R H) (x : H) :
    b.mulOpposite.repr (op x) = b.repr x := rfl

