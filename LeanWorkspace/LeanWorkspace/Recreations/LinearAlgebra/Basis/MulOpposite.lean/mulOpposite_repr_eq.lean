import Mathlib

variable {R H : Type*}

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

theorem mulOpposite_repr_eq (b : Module.Basis ι R H) :
    b.mulOpposite.repr = (opLinearEquiv R).symm.trans b.repr := rfl

