import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem compAddMonoidHom_injective_left (f : A →+ B) (hf : Function.Surjective f) :
    Function.Injective fun ψ : AddChar B M ↦ ψ.compAddMonoidHom f := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

