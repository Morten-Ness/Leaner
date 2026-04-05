import Mathlib

theorem isZero_iff_subsingleton {G : GrpCat} : Limits.IsZero G ↔ Subsingleton G := ⟨fun h ↦ GrpCat.subsingleton_of_isZero h, fun _ ↦ GrpCat.isZero_of_subsingleton G⟩

