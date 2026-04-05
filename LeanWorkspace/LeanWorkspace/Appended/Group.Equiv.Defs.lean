import Mathlib

section

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y := e.toEquiv.apply_eq_iff_eq_symm_apply

end

section

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Function.Bijective f) :
    f ((MulEquiv.ofBijective f hf).symm n) = n := MulEquiv.apply_symm_apply (MulEquiv.ofBijective f hf) n

end

section

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_bijective : Function.Bijective (MulEquiv.symm : (M ≃* N) → N ≃* M) := Function.bijective_iff_has_inverse.mpr ⟨_, MulEquiv.symm_symm, MulEquiv.symm_symm⟩

end

section

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem toMonoidHom_injective : Function.Injective (MulEquiv.toMonoidHom : M ≃* N → M →* N) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end
