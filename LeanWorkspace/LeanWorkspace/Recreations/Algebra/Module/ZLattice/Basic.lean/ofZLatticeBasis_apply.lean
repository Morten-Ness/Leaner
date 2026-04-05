import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

theorem ofZLatticeBasis_apply (i : ι) : b.ofZLatticeBasis K L i = b i := by
  simp [Module.Basis.ofZLatticeBasis]

