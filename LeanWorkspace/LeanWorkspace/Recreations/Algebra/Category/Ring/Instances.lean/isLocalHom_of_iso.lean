import Mathlib

theorem isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom.hom := { map_nonunit := fun a ha => by
      convert f.inv.hom.isUnit_map ha
      simp }

-- see Note [lower instance priority]

