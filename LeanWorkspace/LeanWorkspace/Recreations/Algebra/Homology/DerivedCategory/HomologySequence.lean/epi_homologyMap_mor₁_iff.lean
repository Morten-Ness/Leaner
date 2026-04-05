import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem epi_homologyMap_mor₁_iff :
    Epi ((DerivedCategory.homologyFunctor C n₀).map T.mor₁) ↔ (DerivedCategory.homologyFunctor C n₀).map T.mor₂ = 0 := (DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

