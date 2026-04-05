import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← Submonoid.map_inf _ _ f hf, disjoint_iff.mp h, Submonoid.map_bot]

