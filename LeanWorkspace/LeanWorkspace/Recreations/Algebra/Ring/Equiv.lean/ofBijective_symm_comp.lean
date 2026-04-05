import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem ofBijective_symm_comp (f : R →ₙ+* S) (hf : Function.Bijective f) :
    ((RingEquiv.ofBijective f hf).symm : _ →ₙ+* _).comp f = NonUnitalRingHom.id R := by
  ext
  exact RingEquiv.injective (RingEquiv.ofBijective f hf) <| RingEquiv.apply_symm_apply ..

