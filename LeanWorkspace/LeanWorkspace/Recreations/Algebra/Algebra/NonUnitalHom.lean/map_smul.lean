import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x := map_smulₛₗ _ _ _

