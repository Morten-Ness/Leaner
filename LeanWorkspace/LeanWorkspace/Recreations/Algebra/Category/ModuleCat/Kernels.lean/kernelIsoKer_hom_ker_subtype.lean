import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem kernelIsoKer_hom_ker_subtype :
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation
    (ModuleCat.kernelIsoKer f).hom ≫ ofHom (LinearMap.ker f.hom).subtype = kernel.ι f := IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

