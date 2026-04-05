import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [PerfectField K]

theorem isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H → K} {y : L} (hy : y ∈ rootSpace H α) : S y = α x' • y := by
    replace hy : y ∈ (ad K L x).maxGenEigenspace (α x') :=
      (genWeightSpace_le_genWeightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hy hS₀ hS.isFinitelySemisimple hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H → K) (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ ∈ rootSpace H (α + β) :=
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy, aux hz, aux hyz, smul_lie, lie_smul, ← add_smul, ← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | mem β z hz => exact h_der y z α β hy hz
      | zero => simp
      | add _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
    | zero => simp
    | add _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel
  /- An equivalent form of the derivation axiom used in `LieDerivation`. -/
  replace h_der : ∀ y z : L, S ⁅y, z⁆ = ⁅y, S z⁆ - ⁅z, S y⁆ := by
    simp_rw [← lie_skew (S _) _, add_comm, ← sub_eq_add_neg] at h_der; assumption
  /- Bundle `S` as a `LieDerivation`. -/
  let S' : LieDerivation K L L := ⟨S, h_der⟩
  /- Since `L` has non-degenerate Killing form, `S` must be inner, corresponding to some `y : L`. -/
  obtain ⟨y, hy⟩ := LieDerivation.IsKilling.exists_eq_ad S'
  /- `y` commutes with all elements of `H` because `S` has eigenvalue 0 on `H`, `S = ad K L y`. -/
  have hy' (z : L) (hz : z ∈ H) : ⁅y, z⁆ = 0 := by
    rw [← LieSubalgebra.mem_toLieSubmodule, ← rootSpace_zero_eq] at hz
    simp [S', ← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
  /- Thus `y` belongs to `H` since `H` is self-normalizing. -/
  replace hy' : y ∈ H := by
    suffices y ∈ H.normalizer by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at this
    exact (H.mem_normalizer_iff y).mpr fun z hz ↦ hy' z hz ▸ LieSubalgebra.zero_mem H
  /- It suffices to show `x = y` since `S = ad K L y` is semisimple. -/
  suffices x = y by rwa [this, ← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rw [← sub_eq_zero]
  /- This will follow if we can show that `ad K L (x - y)` is nilpotent. -/
  apply LieAlgebra.IsKilling.eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H (H.sub_mem hx hy')
  /- Which is true because `ad K L (x - y) = N`. -/
  replace hy : S = ad K L y := by rw [← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rwa [map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]

