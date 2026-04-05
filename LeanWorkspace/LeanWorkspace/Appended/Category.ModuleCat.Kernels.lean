import Mathlib

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simpa only [map_add, add_eq_left] using cokernel.condition_apply f m

end

section

variable {R : Type u} [Ring R]

theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) := ⟨fun f => HasColimit.mk ⟨_, ModuleCat.cokernelIsColimit f⟩⟩

end

section

variable {R : Type u} [Ring R]

theorem hasKernels_moduleCat : HasKernels (ModuleCat R) := ⟨fun f => HasLimit.mk ⟨_, ModuleCat.kernelIsLimit f⟩⟩

end

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem kernelIsoKer_hom_ker_subtype :
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation
    (ModuleCat.kernelIsoKer f).hom ≫ ofHom (LinearMap.ker f.hom).subtype = kernel.ι f := IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

end

section

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ofHom (LinearMap.range f.hom).mkQ ≫ (ModuleCat.cokernelIsoRangeQuotient f).inv = cokernel.π f := colimit.isoColimitCocone_ι_inv ⟨_, ModuleCat.cokernelIsColimit f⟩ WalkingParallelPair.one

end
