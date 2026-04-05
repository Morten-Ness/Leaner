import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [HasProduct Z]

theorem piIsoPi_hom_ker_subtype (i : ι) :
    (ModuleCat.piIsoPi Z).hom ≫ ofHom (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) = Pi.π Z i := IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

