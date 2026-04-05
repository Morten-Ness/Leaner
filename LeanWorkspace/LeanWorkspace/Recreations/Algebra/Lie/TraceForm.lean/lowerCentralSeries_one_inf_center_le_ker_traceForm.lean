import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] [IsDomain R]

theorem lowerCentralSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Module.Finite R M] :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L ≤ LinearMap.ker (LieModule.traceForm R L M) := by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z ∈ lowerCentralSeries R L L 1, hzc : z ∈ LieAlgebra.center R L⟩
  ext x
  rw [LieModule.traceForm_apply_apply, LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have that : Module.IsTorsionFree R A := .trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, ← toEnd_baseChange,
    ← toEnd_baseChange]
  replace hz : 1 ⊗ₜ z ∈ lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top, ← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 ⊗ₜ[R] z ∈ LieAlgebra.center A (A ⊗[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u ↦ by simp [hzc u])
      (fun u v hu hv ↦ by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 ⊗ₜ[R] x)
  · exact fun μ ↦ LieModule.trace_toEnd_eq_zero_of_mem_lcs A (A ⊗[R] L)
      (genWeightSpaceOf (A ⊗[R] M) μ ((1 : A) ⊗ₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A ⊗[R] M) hzc (1 ⊗ₜ x)

