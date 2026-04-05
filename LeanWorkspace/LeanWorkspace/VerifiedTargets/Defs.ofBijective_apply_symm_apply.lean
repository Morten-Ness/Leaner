import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Function.Bijective f) :
    f ((MulEquiv.ofBijective f hf).symm n) = n := MulEquiv.apply_symm_apply (MulEquiv.ofBijective f hf) n

