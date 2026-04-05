import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem shiftMap_homologyFunctor_map_Qh
    {K L : HomotopyCategory C (.up ℤ)} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a' := by lia) :
    (DerivedCategory.homologyFunctor C 0).shiftMap (ShiftedHom.map f Qh) a a' h =
    (DerivedCategory.homologyFunctorFactorsh C a).hom.app _ ≫
      (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (DerivedCategory.homologyFunctorFactorsh C a').inv.app _ :=
  Functor.ShiftSequence.induced_shiftMap ..

