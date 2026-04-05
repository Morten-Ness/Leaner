import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
    (t : IsSl2Triple h e f) (hte : e ∈ rootSpace H α) (htf : f ∈ rootSpace H (-α)) {x : L} :
    x ∈ LieAlgebra.IsKilling.sl2SubalgebraOfRoot hα ↔ ∃ c₁ c₂ c₃ : K, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp only [LieAlgebra.IsKilling.sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : ∃ c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα) ⟨_, he.choose_spec.choose_spec.2.1⟩
    exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨cf, hcf⟩ : ∃ c : K, hf.choose = c • f := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, htf⟩ (by simpa using t.f_ne_zero)).mp
      (LieAlgebra.IsKilling.finrank_rootSpace_eq_one (-α) (by simpa)) ⟨_, hf.choose_spec.2.2⟩
    exact ⟨c, by simpa using hc.symm⟩
  have hce₀ : ce ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hce
    exact he.choose_spec.choose_spec.1.e_ne_zero hce
  have hcf₀ : cf ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hcf
    exact he.choose_spec.choose_spec.1.f_ne_zero hcf
  simp_rw [hcf, hce]
  refine ⟨fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce, c₂ * cf, c₃ * cf * ce, ?_⟩,
    fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce⁻¹, c₂ * cf⁻¹, c₃ * ce⁻¹ * cf⁻¹, ?_⟩⟩
  · simp [hx, mul_smul]
  · simp [hx, mul_smul, hce₀, hcf₀]

