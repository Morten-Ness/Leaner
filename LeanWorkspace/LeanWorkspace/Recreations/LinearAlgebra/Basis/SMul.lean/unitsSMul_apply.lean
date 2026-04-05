import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem unitsSMul_apply {v : Module.Basis ι R M} {w : ι → Rˣ} (i : ι) : Module.Basis.unitsSMul v w i = w i • v i := mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (Module.Basis.units_smul_span_eq_top v.span_eq).ge i

