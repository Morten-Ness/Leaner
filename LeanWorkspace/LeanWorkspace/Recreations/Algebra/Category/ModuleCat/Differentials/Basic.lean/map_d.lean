import Mathlib

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

theorem map_d (b : B) : CommRingCat.KaehlerDifferential.map fac (ModuleCat.Derivation.d b) = ModuleCat.Derivation.d (g' b) := by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

