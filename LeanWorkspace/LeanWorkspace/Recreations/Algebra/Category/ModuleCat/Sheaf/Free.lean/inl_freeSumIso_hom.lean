import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (I J : Type u)

theorem inl_freeSumIso_hom :
    coprod.inl ≫ (SheafOfModules.freeSumIso (R := R) I J).hom = SheafOfModules.freeMap Sum.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (SheafOfModules.free (R := R) I) (SheafOfModules.free J)) _ (.mk .left)

