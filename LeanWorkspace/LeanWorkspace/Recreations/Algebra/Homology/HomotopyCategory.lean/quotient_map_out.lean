import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (HomotopyCategory.quotient V c).map f.out = f := Quot.out_eq _

