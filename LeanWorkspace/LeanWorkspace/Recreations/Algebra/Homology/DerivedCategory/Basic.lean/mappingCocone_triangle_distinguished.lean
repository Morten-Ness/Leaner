import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

variable {C} {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem mappingCocone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ) ∈ distTriang _ := by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

