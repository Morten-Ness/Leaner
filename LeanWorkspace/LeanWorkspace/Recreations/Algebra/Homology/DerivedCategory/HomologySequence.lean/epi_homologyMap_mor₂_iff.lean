import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem epi_homologyMap_mor₂_iff (h : n₀ + 1 = n₁ := by lia) :
    Epi ((DerivedCategory.homologyFunctor C n₀).map T.mor₂) ↔ DerivedCategory.HomologySequence.δ T n₀ n₁ h = 0 :=
  (DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h

