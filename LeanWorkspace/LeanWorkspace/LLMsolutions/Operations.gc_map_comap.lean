import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem gc_map_comap (f : F) : GaloisConnection (Submonoid.map f) (Submonoid.comap f) := by
  intro A B
  constructor
  · intro h a ha
    exact h ⟨a, ha, rfl⟩
  · intro h b hb
    rcases hb with ⟨a, ha, rfl⟩
    exact h ha
