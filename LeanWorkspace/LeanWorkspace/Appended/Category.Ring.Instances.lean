import Mathlib

section

theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) := ⟨fun _ _ h => CommRingCat.hom_ext <| ringHom_ext M congr(($h).hom)⟩

end

section

theorem isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom.hom := { map_nonunit := fun a ha => by
      convert f.inv.hom.isUnit_map ha
      simp }

-- see Note [lower instance priority]

end
