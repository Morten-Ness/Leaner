import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

variable {C} {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem mappingCone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle φ) ∈ distTriang _ := by
  rw [DerivedCategory.mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

