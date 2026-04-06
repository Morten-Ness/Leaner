import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def {H₁ H₂ : Subgroup G} : Disjoint H₁ H₂ ↔ ∀ {x : G}, x ∈ H₁ → x ∈ H₂ → x = 1 := by
  constructor
  · intro h x hx1 hx2
    have hx : x ∈ H₁ ⊓ H₂ := ⟨hx1, hx2⟩
    have hx' : x ∈ (⊥ : Subgroup G) := by
      rw [disjoint_iff] at h
      simpa [h] using hx
    simpa using hx'
  · intro h
    rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      have hx1 : x ∈ H₁ := hx.1
      have hx2 : x ∈ H₂ := hx.2
      have : x = 1 := h hx1 hx2
      simpa [this]
    · intro hx
      have : x = 1 := by simpa using hx
      subst x
      exact ⟨H₁.one_mem, H₂.one_mem⟩
