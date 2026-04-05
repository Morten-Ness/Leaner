import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable (M N : ModuleCat.{v} R)

theorem smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGrpCat).map f := by
  ext x
  exact (f.hom.map_smul r x).symm

