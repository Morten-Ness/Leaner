import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a
