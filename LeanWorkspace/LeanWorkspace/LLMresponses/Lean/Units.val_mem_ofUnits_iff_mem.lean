import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) ∈ H.ofUnits ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := Units.ext hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩
