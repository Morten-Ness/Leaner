import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

theorem ofZLatticeBasis_repr_apply (x : L) (i : ι) :
    (b.ofZLatticeBasis K L).repr x i = b.repr x i := by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars ℤ) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap ℤ K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Module.Basis.ext b fun i ↦ ?_
  simp_rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coe_subtype, ← Module.Basis.ofZLatticeBasis_apply b K, repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]

