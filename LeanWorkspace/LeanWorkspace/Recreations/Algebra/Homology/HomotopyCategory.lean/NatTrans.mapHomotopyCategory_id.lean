import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

variable {V} {W : Type*} [Category* W] [Preadditive W]

theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    CategoryTheory.NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by cat_disch

