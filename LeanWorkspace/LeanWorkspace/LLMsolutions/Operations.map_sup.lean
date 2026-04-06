FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    change f y ∈ S.map f ⊔ T.map f
    rcases hy with ⟨s, hs, t, ht, rfl⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, f t, ⟨t, ht, rfl⟩, by simpa using map_mul f s t⟩
  · intro hx
    change x ∈ (S.map f ⊔ T.map f) at hx
    rcases hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨s, hs, rfl⟩
    rcases hz with ⟨t, ht, rfl⟩
    refine ⟨s * t, ?_, by simpa using (map_mul f s t).symm⟩
    exact ⟨s, hs, t, ht, rfl⟩
