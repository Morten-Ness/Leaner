import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quotient_obj_as (C : HomologicalComplex V c) : ((HomotopyCategory.quotient V c).obj C).as = C := rfl

