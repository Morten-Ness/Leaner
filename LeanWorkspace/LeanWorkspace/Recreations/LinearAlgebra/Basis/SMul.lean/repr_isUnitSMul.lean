import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem repr_isUnitSMul {v : Module.Basis ι R₂ M} {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i := Module.Basis.repr_unitsSMul _ _ _ _

