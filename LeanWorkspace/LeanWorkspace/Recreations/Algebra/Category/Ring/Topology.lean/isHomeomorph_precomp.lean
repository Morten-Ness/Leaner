import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem isHomeomorph_precomp (f : A ⟶ B) [IsIso f] :
    IsHomeomorph ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := (CommRingCat.HomTopology.precompHomeomorph (asIso f)).isHomeomorph

