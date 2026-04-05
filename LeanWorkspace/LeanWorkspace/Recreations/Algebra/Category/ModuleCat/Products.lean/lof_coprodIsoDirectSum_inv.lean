import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [DecidableEq ι]

variable [HasCoproduct Z]

theorem lof_coprodIsoDirectSum_inv (i : ι) :
    ofHom (DirectSum.lof R ι (fun i ↦ Z i) i) ≫ (ModuleCat.coprodIsoDirectSum Z).inv = Sigma.ι Z i := (ModuleCat.coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

