import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

set_option backward.isDefEq.respectTransparency false in
theorem exists_forall_abs_repr_le_norm :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L), ∀ i, ε * |b.repr x i| ≤ ‖x‖ := by
  wlog H : IsZLattice ℝ L
  · let E' := Submodule.span ℝ (L : Set E)
    let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
      Submodule.subset_span
    have inst : IsZLattice ℝ L' :=
      ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
    obtain ⟨ε, hε, H⟩ := this (b.map e.symm) inst
    exact ⟨ε, hε, fun x i ↦ by simpa using H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Module.Basis ι ℝ E := Module.Basis.ofZLatticeBasis ℝ L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := ℝ))
  have := e.continuous.1 (Set.univ.pi fun _ ↦ Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε / 2, by positivity, fun x i ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hx : ‖x.1‖ ≠ 0 := by simpa
  have : |ε / 2 * (‖↑x‖⁻¹ * (b.repr x) i)| < 1 := by
    simpa [e, b', ← abs_lt] using @hε' ((ε / 2) • ‖x‖⁻¹ • x)
      (by simpa [norm_smul, inv_mul_cancel₀ hx, abs_eq_self.mpr hε.le]) i trivial
  rw [abs_mul, abs_mul, abs_inv, mul_left_comm, abs_norm, inv_mul_lt_iff₀ (by positivity),
    mul_one, abs_eq_self.mpr (by positivity), ← Int.cast_abs] at this
  exact this.le

