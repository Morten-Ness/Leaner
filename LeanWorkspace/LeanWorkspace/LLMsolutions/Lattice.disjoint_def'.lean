import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def' {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x = y → x = 1 := by
  constructor
  · intro h x y hx hy hxy
    have hbot : H₁ ⊓ H₂ = (⊥ : Subgroup G) := disjoint_iff.mp h
    have hx' : x ∈ H₁ ⊓ H₂ := ⟨hx, hxy ▸ hy⟩
    have hx'' : x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hx'
    exact hx''
  · intro h
    rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      exact h hx.1 hx.2 rfl
    · intro hx
      have hx1 : x = 1 := hx
      subst hx1
      exact ⟨H₁.one_mem, H₂.one_mem⟩
