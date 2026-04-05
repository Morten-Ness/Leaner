import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

variable [DistribMulAction R B]

variable [DistribMulAction R C]

theorem prod_fst_snd : NonUnitalAlgHom.prod (NonUnitalAlgHom.fst R A B) (NonUnitalAlgHom.snd R A B) = 1 := NonUnitalAlgHom.coe_injective Pi.prod_fst_snd

