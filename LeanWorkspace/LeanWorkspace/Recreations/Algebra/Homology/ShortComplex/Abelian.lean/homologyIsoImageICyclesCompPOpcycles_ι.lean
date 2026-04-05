import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

theorem homologyIsoImageICyclesCompPOpcycles_ι :
    S.homologyIsoImageICyclesCompPOpcycles.hom ≫ image.ι (S.iCycles ≫ S.pOpcycles) =
      S.homologyι := image.isoStrongEpiMono_hom_comp_ι _ _ _

