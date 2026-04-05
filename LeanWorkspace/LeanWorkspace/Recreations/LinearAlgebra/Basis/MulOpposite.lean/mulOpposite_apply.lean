import Mathlib

variable {R H : Type*}

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

theorem mulOpposite_apply (b : Module.Basis ι R H) (i : ι) :
    b.mulOpposite i = op (b i) := rfl

