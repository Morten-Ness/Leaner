import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by
  constructor
  · intro hx
    rcases hx with ⟨u, hu, rfl⟩
    simpa using hu
  · intro hx
    exact ⟨toUnits x, hx, by simp⟩
