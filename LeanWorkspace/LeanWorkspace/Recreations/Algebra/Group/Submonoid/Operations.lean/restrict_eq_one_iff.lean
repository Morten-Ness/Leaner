import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem restrict_eq_one_iff {N S : Type*} [MulOneClass N] {f : M →* N} [SetLike S M]
    [SubmonoidClass S M] {s : S} :
    f.restrict s = 1 ↔ ∀ x ∈ s, f x = 1 := by
  simp [MonoidHom.ext_iff]

