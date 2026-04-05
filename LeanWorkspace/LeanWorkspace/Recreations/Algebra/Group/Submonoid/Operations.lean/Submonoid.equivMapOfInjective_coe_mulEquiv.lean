import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem Submonoid.equivMapOfInjective_coe_mulEquiv (e : M ≃* N) :
    S.equivMapOfInjective (e : M →* N) (EquivLike.injective e) = e.submonoidMap S := by
  ext
  rfl

