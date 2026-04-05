import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (HomotopyCategory.quotient V c).map f = (HomotopyCategory.quotient V c).map g := CategoryTheory.Quotient.sound _ ⟨h⟩

