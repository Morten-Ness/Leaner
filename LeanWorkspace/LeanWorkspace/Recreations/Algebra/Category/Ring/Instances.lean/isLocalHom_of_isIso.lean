import Mathlib

theorem isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalHom f.hom := isLocalHom_of_iso (asIso f)

