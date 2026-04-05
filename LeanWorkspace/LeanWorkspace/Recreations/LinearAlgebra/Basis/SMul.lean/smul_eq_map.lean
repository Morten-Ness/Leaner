import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable [Group G] [Group G']

variable [DistribMulAction G M] [DistribMulAction G' M]

variable [SMulCommClass G R M] [SMulCommClass G' R M]

theorem smul_eq_map (g : M ≃ₗ[R] M) (b : Module.Basis ι R M) : g • b = b.map g := rfl

