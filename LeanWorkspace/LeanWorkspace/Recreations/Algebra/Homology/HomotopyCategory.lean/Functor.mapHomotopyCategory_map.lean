import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

variable {V} {W : Type*} [Category* W] [Preadditive W]

theorem Functor.mapHomotopyCategory_map (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (F.mapHomotopyCategory c).map ((HomotopyCategory.quotient V c).map f) =
      (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map f) := rfl

