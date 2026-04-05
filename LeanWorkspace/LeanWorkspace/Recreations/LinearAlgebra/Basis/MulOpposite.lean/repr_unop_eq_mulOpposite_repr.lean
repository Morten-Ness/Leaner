import Mathlib

variable {R H : Type*}

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

theorem repr_unop_eq_mulOpposite_repr (b : Module.Basis ι R H) (x : Hᵐᵒᵖ) :
    b.repr (unop x) = b.mulOpposite.repr x := rfl

