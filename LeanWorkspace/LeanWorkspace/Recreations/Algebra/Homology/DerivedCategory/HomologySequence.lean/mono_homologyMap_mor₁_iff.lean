import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem mono_homologyMap_mor₁_iff (h : n₀ + 1 = n₁ := by lia) :
    Mono ((DerivedCategory.homologyFunctor C n₁).map T.mor₁) ↔ DerivedCategory.HomologySequence.δ T n₀ n₁ h = 0 :=
  (DerivedCategory.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

