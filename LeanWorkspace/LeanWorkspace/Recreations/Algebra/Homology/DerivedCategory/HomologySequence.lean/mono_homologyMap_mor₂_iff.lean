import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem mono_homologyMap_mor₂_iff :
    Mono ((DerivedCategory.homologyFunctor C n₀).map T.mor₂) ↔ (DerivedCategory.homologyFunctor C n₀).map T.mor₁ = 0 := (DerivedCategory.homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

