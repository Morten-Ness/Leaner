import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨u, huS, rfl⟩
    refine ⟨u.isUnit, ?_⟩
    simpa using huS
  · rintro ⟨h, hhS⟩
    exact ⟨h.unit, by simpa using hhS, by simp⟩
