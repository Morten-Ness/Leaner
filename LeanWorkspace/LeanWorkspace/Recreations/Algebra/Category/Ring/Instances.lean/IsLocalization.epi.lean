import Mathlib

theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) := ⟨fun _ _ h => CommRingCat.hom_ext <| ringHom_ext M congr(($h).hom)⟩

