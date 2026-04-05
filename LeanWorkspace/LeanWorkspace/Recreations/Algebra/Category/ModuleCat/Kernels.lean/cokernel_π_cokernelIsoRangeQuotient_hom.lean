import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (ModuleCat.cokernelIsoRangeQuotient f).hom = ofHom (LinearMap.range f.hom).mkQ := colimit.isoColimitCocone_ι_hom _ _

