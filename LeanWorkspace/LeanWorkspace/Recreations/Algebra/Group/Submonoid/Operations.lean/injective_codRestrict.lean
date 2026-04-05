import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S)
    (h : ∀ x, f x ∈ s) : Function.Injective (f.codRestrict s h) ↔ Function.Injective f := ⟨fun H _ _ hxy ↦ H <| Subtype.ext hxy, fun H _ _ hxy ↦ H (congr_arg Subtype.val hxy)⟩

