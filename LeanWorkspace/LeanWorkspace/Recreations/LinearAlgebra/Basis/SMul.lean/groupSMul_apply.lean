import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Module.Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i := mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (Module.Basis.groupSMul_span_eq_top v.span_eq).ge i

