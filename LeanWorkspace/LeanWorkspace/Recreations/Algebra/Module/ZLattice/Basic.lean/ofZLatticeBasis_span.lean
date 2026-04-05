import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

theorem ofZLatticeBasis_span : span ℤ (Set.range (b.ofZLatticeBasis K)) = L := by
  calc span ℤ (Set.range (b.ofZLatticeBasis K))
    _ = span ℤ (L.subtype '' Set.range b) := by congr; ext; simp
    _ = ZSpan.map L.subtype (span ℤ (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

