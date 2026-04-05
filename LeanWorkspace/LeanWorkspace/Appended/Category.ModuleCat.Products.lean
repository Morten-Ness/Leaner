import Mathlib

section

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [DecidableEq ι]

variable [HasCoproduct Z]

theorem lof_coprodIsoDirectSum_inv (i : ι) :
    ofHom (DirectSum.lof R ι (fun i ↦ Z i) i) ≫ (ModuleCat.coprodIsoDirectSum Z).inv = Sigma.ι Z i := (ModuleCat.coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

end

section

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [HasProduct Z]

theorem piIsoPi_hom_ker_subtype (i : ι) :
    (ModuleCat.piIsoPi Z).hom ≫ ofHom (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) = Pi.π Z i := IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

end
