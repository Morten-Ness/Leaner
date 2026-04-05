import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g := HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

