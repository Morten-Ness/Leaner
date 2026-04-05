import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable (M N : ModuleCat.{v} R)

variable {M N}
  (φ : (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N)
  (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

theorem forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (ModuleCat.homMk φ hφ) = φ := rfl

