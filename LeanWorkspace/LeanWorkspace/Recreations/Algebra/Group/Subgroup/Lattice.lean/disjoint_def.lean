import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

variable {P : C → Prop}

theorem disjoint_def {H₁ H₂ : Subgroup G} : Disjoint H₁ H₂ ↔ ∀ {x : G}, x ∈ H₁ → x ∈ H₂ → x = 1 := disjoint_iff_inf_le.trans <| by simp only [SetLike.le_def, Subgroup.mem_inf, Subgroup.mem_bot, and_imp]

