import Mathlib

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp {φ : M →* N} {ψ : N →* P} :
    MonoidHom.CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl

