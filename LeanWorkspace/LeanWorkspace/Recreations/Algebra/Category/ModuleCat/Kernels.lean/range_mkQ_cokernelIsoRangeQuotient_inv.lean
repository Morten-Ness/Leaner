import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ofHom (LinearMap.range f.hom).mkQ ≫ (ModuleCat.cokernelIsoRangeQuotient f).inv = cokernel.π f := colimit.isoColimitCocone_ι_inv ⟨_, ModuleCat.cokernelIsColimit f⟩ WalkingParallelPair.one

