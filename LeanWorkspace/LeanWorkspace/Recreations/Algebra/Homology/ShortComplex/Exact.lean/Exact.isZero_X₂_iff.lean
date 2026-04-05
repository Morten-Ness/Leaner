import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem Exact.isZero_X₂_iff (hS : S.Exact) : IsZero S.X₂ ↔ S.f = 0 ∧ S.g = 0 := by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

