import Mathlib

theorem isZero_iff_subsingleton {G : CommGrpCat} : Limits.IsZero G ↔ Subsingleton G := ⟨fun h ↦ CommGrpCat.subsingleton_of_isZero h, fun _ ↦ CommGrpCat.isZero_of_subsingleton G⟩

