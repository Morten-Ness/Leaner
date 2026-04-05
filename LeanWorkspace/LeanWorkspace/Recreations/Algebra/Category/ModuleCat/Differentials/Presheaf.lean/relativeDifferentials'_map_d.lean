import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

theorem relativeDifferentials'_map_d {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    DFunLike.coe (α := CommRingCat.KaehlerDifferential (φ'.app X))
      (β := fun _ ↦ CommRingCat.KaehlerDifferential (φ'.app Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ').map f))
        (CommRingCat.KaehlerDifferential.d x) =
        CommRingCat.KaehlerDifferential.d (R.map f x) :=
  CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _

