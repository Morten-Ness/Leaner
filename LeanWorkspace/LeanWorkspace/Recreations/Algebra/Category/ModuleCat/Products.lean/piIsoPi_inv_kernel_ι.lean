import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

variable [HasProduct Z]

theorem piIsoPi_inv_kernel_ι (i : ι) :
    (ModuleCat.piIsoPi Z).inv ≫ Pi.π Z i = ofHom (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i) := limit.isoLimitCone_inv_π _ _

