import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Function.Injective ψ) :
    Function.Injective fun f : A →+ B ↦ ψ.compAddMonoidHom f := by
  intro f g h
  ext a
  apply hψ
  have := DFunLike.congr_fun h a
  simpa using this
