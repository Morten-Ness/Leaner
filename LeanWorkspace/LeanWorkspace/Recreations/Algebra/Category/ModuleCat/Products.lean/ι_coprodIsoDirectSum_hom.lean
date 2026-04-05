import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [DecidableEq ι]

variable [HasCoproduct Z]

theorem ι_coprodIsoDirectSum_hom (i : ι) :
    Sigma.ι Z i ≫ (ModuleCat.coprodIsoDirectSum Z).hom = ofHom (DirectSum.lof R ι (fun i ↦ Z i) i) := colimit.isoColimitCocone_ι_hom _ _

