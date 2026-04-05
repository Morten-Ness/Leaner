import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem kernelIsoKer_inv_kernel_ι : (ModuleCat.kernelIsoKer f).inv ≫ kernel.ι f =
    ofHom (LinearMap.ker f.hom).subtype := limit.isoLimitCone_inv_π _ _

