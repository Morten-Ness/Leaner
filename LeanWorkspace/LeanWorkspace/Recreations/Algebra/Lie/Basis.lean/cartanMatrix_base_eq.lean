import Mathlib

variable {ι K L : Type*} [Fintype ι] [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] (b : Basis ι K L)

variable [IsTriangularizable K b.cartan L] [IsKilling K L]

private theorem cartan_lie_mem_lieSpan_e {x y : L}
    (hx : x ∈ b.cartan) (hy : y ∈ lieSpan R L (Set.range b.e)) :
    ⁅x, y⁆ ∈ lieSpan R L (Set.range b.e) := by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule, coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
      apply zsmul_mem <| subset_lieSpan <| mem_range_self i
    | zero => simp
    | add v w _ _ hv hw => simpa using add_mem hv hw
    | smul t v _ hv => simpa using LieSubalgebra.smul_mem _ t hv
  | zero => simp
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul t u _ hu => simpa using LieSubalgebra.smul_mem _ t hu
  | lie u v hu hv hu' hv' =>
    rw [leibniz_lie, ← lie_skew _ v, neg_add_eq_sub]
    exact sub_mem (LieSubalgebra.lie_mem _ hu hv') (LieSubalgebra.lie_mem _ hv hu')


private theorem iSup_cartan_borelLower_borelUpper_eq_top_aux
    {y z : L} (hy : y ∈ lieSpan R L (Set.range b.e)) (hz : z ∈ lieSpan R L (Set.range b.f)) :
    ⁅y, z⁆ ∈ b.cartan.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper := by
  have (i : ι) (x : L) (hx : x ∈ lieSpan R L (Set.range b.f)) :
      ⁅b.e i, x⁆ ∈ b.cartan.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]
        apply LieSubmodule.mem_sup_left
        rw [b.cartan_eq_lieSpan, mem_toLieSubmodule]
        exact LieSubalgebra.subset_lieSpan <| mem_range_self i
      · simp [b.lie_e_f_ne _ _ hij]
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact add_mem hu hv
    | smul t u _ hu => rw [lie_smul]; exact SMulMemClass.smul_mem t hu
    | lie u v hu hv hu' hv' =>
      obtain ⟨w₁, hw₁, w₂, hw₂, hwu⟩ : ∃ y ∈ b.cartan, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, u⁆ := by
        simpa only [LieSubmodule.mem_sup] using hu'
      obtain ⟨w₃, hw₃, w₄, hw₄, hwv⟩ : ∃ y ∈ b.cartan, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, v⁆ := by
        simpa only [LieSubmodule.mem_sup] using hv'
      rw [leibniz_lie, ← hwu, ← hwv, lie_add, add_lie, ← add_assoc]
      repeat apply add_mem
      · exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₁, hw₁⟩) hv
      · exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₂ hv
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₃, hw₃⟩) hu
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₄ hu
  induction hy using lieSpan_induction generalizing z with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact LieSubmodule.mem_sup_left <| this i z hz
  | zero => simp
  | add u v _ _ hu hv => rw [add_lie]; exact add_mem (hu hz) (hv hz)
  | smul t u _ hu => rw [smul_lie]; exact SMulMemClass.smul_mem t (hu hz)
  | lie u v hu hv hu' hv' =>
    rw [lie_lie]
    apply sub_mem
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ b.cartan) (yl ∈ lieSpan R L (Set.range b.f)) (yu ∈ lieSpan R L (Set.range b.e)),
        yc + yl + yu = ⁅v, z⁆ := by simpa [LieSubmodule.mem_sup] using hv' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hu
      · exact hu' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <|  LieSubalgebra.lie_mem _ hyu hu
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ b.cartan) (yl ∈ lieSpan R L (Set.range b.f)) (yu ∈ lieSpan R L (Set.range b.e)),
        yc + yl + yu = ⁅u, z⁆ := by simpa [LieSubmodule.mem_sup] using hu' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hv
      · exact hv' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <|  LieSubalgebra.lie_mem _ hyu hv


private theorem cartan_borelLower_borelUpper_le :
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • b.baseSupp i)
    ![b.cartan.toLieSubmodule, b.borelLower, b.borelUpper] ≤ ![rootSpace b.cartan 0, U, V] := by
  intro i
  fin_cases i
  · exact toLieSubmodule_le_rootSpace_zero R L b.cartan
  · exact LieAlgebra.Basis.borelLower_le_biSup b
  · exact LieAlgebra.Basis.borelUpper_le_biSup b


theorem cartanMatrix_base_eq :
    b.base.cartanMatrix = b.A.reindex b.baseSupportEquiv b.baseSupportEquiv := by
  suffices b.base.cartanMatrix.reindex b.baseSupportEquiv.symm b.baseSupportEquiv.symm = b.A by
    rwa [← (Matrix.reindex b.baseSupportEquiv b.baseSupportEquiv).symm_apply_eq]
  ext i j
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [reindex_apply, submatrix_apply, RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  simp [← Weight.coe_coe]

