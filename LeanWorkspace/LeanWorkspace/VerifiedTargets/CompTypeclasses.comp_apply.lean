import Mathlib

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp_apply
    {φ : M →* N} {ψ : N →* P} {χ : M →* P} (h : MonoidHom.CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, MonoidHom.comp_apply]

