import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem isUnitSMul_apply {v : Module.Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i := Module.Basis.unitsSMul_apply i

