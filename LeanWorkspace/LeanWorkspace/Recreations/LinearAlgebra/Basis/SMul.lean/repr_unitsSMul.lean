import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem repr_unitsSMul (e : Module.Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i := congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (Module.Basis.coord_unitsSMul e w i)

