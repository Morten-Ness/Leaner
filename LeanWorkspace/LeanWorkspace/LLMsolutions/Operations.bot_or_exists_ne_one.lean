import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) := by
  by_cases h : S = ⊥
  · exact Or.inl h
  · right
    by_contra h'
    apply h
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · subst hx1
        exact Submonoid.mem_bot.2 rfl
      · exfalso
        exact h' ⟨x, hx, hx1⟩
    · intro hx
      exact Submonoid.mem_carrier.mp hx ▸ S.one_mem
