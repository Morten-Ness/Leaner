import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

set_option backward.isDefEq.respectTransparency false in
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (HomotopyCategory.quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by simp

