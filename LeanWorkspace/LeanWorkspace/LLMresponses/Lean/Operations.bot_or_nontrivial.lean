FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  by_cases h : S = ⊥
  · exact Or.inl h
  · right
    classical
    by_contra hnt
    apply h
    ext x
    constructor
    · intro hx
      have hs : (⟨x, hx⟩ : S) = 1 := by
        have hsub : Subsingleton S := not_nontrivial_iff_subsingleton.mp hnt
        exact hsub.elim ⟨x, hx⟩ 1
      change x = 1 at hs
      simpa [hs] using (show x ∈ (⊥ : Submonoid M) from by simp)
    · intro hx
      simpa using hx
