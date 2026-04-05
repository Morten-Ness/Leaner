import Mathlib

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact)

theorem singleTriangle_distinguished :
    hS.singleTriangle ∈ distTriang (DerivedCategory C) := isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))) _ (CategoryTheory.ShortComplex.ShortExact.singleTriangleIso hS)

end
