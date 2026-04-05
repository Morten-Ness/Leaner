import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

set_option backward.isDefEq.respectTransparency false in
theorem Real.finrank_eq_int_finrank_of_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : DiscreteTopology (span ℤ s)) :
    Set.finrank ℝ s = Set.finrank ℤ s := by
  let F := span ℝ s
  let L : Submodule ℤ (span ℝ s) := comap (F.restrictScalars ℤ).subtype (span ℤ s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars ℤ ℝ s)
  have : DiscreteTopology L := by
    let e : span ℤ s ≃L[ℤ] L :=
      ⟨f.symm, continuous_of_discreteTopology, Isometry.continuous fun _ ↦ congrFun rfl⟩
    exact e.toHomeomorph.discreteTopology
  have : IsZLattice ℝ L := ⟨eq_top_iff.mpr <|
    span_span_coe_preimage.symm.le.trans (span_mono (Set.preimage_mono subset_span))⟩
  rw [Set.finrank, Set.finrank, ← f.finrank_eq]
  exact (ZLattice.rank ℝ L).symm

