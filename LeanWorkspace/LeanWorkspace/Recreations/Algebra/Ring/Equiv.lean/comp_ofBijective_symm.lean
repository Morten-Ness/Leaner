import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem comp_ofBijective_symm (f : R →ₙ+* S) (hf : Function.Bijective f) :
    f.comp ((RingEquiv.ofBijective f hf).symm : _ →ₙ+* _) = NonUnitalRingHom.id S := by
  ext
  exact RingEquiv.injective (RingEquiv.ofBijective f hf).symm <| RingEquiv.apply_symm_apply ..

