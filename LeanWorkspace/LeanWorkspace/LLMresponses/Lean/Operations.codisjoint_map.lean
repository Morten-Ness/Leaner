FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) :
    Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff]
  ext y
  constructor
  · intro hy
    trivial
  · intro _
    rcases hf y with ⟨x, rfl⟩
    have htop : H ⊔ K = ⊤ := by
      simpa [codisjoint_iff] using h
    have hx : x ∈ (H ⊔ K : Submonoid M) := by
      simp [htop]
    rcases show ∃ a ∈ H, ∃ b ∈ K, a * b = x from Submonoid.mem_sup.mp hx with
      ⟨a, ha, b, hb, habx⟩
    exact Submonoid.mem_sup.mpr ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, by
      simpa [habx] using map_mul f a b⟩
