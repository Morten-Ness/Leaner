import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) :
    Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff, ← Submonoid.map_sup, codisjoint_iff.mp h, ← MonoidHom.mrange_eq_map,
    MonoidHom.mrange_eq_top_of_surjective _ hf]

