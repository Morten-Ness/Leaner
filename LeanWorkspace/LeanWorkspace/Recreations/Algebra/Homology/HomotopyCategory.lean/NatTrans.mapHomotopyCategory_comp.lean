import Mathlib

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

variable {V} {W : Type*} [Category* W] [Preadditive W]

theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    CategoryTheory.NatTrans.mapHomotopyCategory (α ≫ β) c =
      CategoryTheory.NatTrans.mapHomotopyCategory α c ≫ CategoryTheory.NatTrans.mapHomotopyCategory β c := by cat_disch

