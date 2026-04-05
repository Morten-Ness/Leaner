import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem map_add (f : A →ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y := map_add _ _ _

