import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quot_mk_eq_quotient_map {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Quot.mk _ f = (HomotopyCategory.quotient V c).map f := rfl

