import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
  [ProperSpace F]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

theorem Module.Basis.ofZLatticeBasis_comap (e : F ≃L[K] E) {ι : Type*} (b : Module.Basis ι ℤ L) :
    (b.ofZLatticeComap K L e.toLinearEquiv).ofZLatticeBasis K (ZLattice.comap K L e.toLinearMap) =
    ZSpan.map (b.ofZLatticeBasis K L) e.symm.toLinearEquiv := by
  ext
  simp

