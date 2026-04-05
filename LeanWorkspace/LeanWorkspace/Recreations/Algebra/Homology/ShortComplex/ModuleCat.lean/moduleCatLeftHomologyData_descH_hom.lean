import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCatLeftHomologyData_descH_hom {M : ModuleCat R}
    (φ : S.moduleCatLeftHomologyData.K ⟶ M) (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) :
    (S.moduleCatLeftHomologyData.descH φ h).hom =
      (LinearMap.range <| ModuleCat.Hom.hom _).liftQ
         φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h) := rfl

