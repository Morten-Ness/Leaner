import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_exists_ne_one (H : Subgroup G) : Nontrivial H ↔ ∃ x ∈ H, x ≠ (1 : G) := by
  constructor
  · intro h
    rcases exists_ne (1 : H) with ⟨x, hx⟩
    refine ⟨x, x.property, ?_⟩
    intro h1
    apply hx
    ext
    simpa using h1
  · rintro ⟨x, hxH, hx1⟩
    refine ⟨⟨x, hxH⟩, 1, ?_⟩
    intro h
    apply hx1
    exact congrArg Subtype.val h
