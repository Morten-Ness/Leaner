import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [Submonoid.disjoint_def] at h ⊢
  intro x hxH hxK
  rcases hxH with ⟨y, hy, rfl⟩
  rcases hxK with ⟨z, hz, hzEq⟩
  have hyz : y = z := hf hzEq.symm
  subst hyz
  rw [← map_one f]
  exact congrArg f (h hy hz)
