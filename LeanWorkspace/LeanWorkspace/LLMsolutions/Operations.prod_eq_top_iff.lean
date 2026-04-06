import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  constructor
  · intro h
    constructor
    · ext x
      constructor
      · intro hx
        trivial
      · intro hx
        have hmem : (x, (1 : N)) ∈ s.prod t := by
          rw [h]
          trivial
        exact hmem.1
    · ext y
      constructor
      · intro hy
        trivial
      · intro hy
        have hmem : ((1 : M), y) ∈ s.prod t := by
          rw [h]
          trivial
        exact hmem.2
  · rintro ⟨hs, ht⟩
    rw [hs, ht]
    ext x
    constructor <;> intro hx <;> trivial
