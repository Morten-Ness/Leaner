import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def' {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x = y → x = 1 := Subgroup.disjoint_def.trans ⟨fun h _x _y hx hy hxy ↦ h hx <| hxy.symm ▸ hy, fun h _x hx hx' ↦ h hx hx' rfl⟩

