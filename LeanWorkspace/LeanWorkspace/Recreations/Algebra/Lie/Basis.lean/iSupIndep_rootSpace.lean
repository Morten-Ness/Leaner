import Mathlib

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

variable [Fintype ι]

variable [IsDomain R] [CharZero R]

variable [IsTorsionFree R L]

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


theorem iSupIndep_rootSpace :
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace b.cartan 0, U, V] := by
  set U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • (-b.baseSupp) i) with hU
  set V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • b.baseSupp i) with hV
  set s0 : Set (b.cartan → R) := {0} with hs0
  set sU : Set (b.cartan → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • (-b.baseSupp) i} with hsU
  set sV : Set (b.cartan → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • b.baseSupp i} with hsV
  have hs0' : rootSpace b.cartan 0 = ⨆ i ∈ s0, LieModule.genWeightSpace L i := by simp [hs0]
  have hsU' : U = ⨆ i ∈ sU, LieModule.genWeightSpace L i := by
    simp only [hU, hsU, mem_setOf_eq, iSup_exists, iSup_and, iSup_comm (ι := b.cartan → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hsV' : V = ⨆ i ∈ sV, LieModule.genWeightSpace L i := by
    simp only [hV, hsV, mem_setOf_eq, iSup_exists, iSup_and, iSup_comm (ι := b.cartan → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hU0 : Disjoint s0 sU := by
    suffices ∀ g ∈ sU, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hg
    rw [neg_eq_zero, LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp LieAlgebra.Basis.linearIndependent_baseSupp b ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hV0 : Disjoint s0 sV := by
    suffices ∀ g ∈ sV, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = ∑ i, n i • b.baseSupp i := by
      simpa [hsV] using hg
    rw [LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp LieAlgebra.Basis.linearIndependent_baseSupp b ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hUV : Disjoint sU sV := by
    refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
    rintro rfl
    obtain ⟨n, hn, hn'⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ f = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hf
    obtain ⟨m, hm, rfl⟩ : ∃ m : ι → ℕ, m ≠ 0 ∧ f = ∑ i, m i • b.baseSupp i := by
      simpa [hsV] using hg
    replace hn' : ∑ i, (((↑) : ℕ → R) ∘ (m + n)) i • b.baseSupp i = 0 := by
      rw [eq_neg_iff_add_eq_zero] at hn'
      change ⇑(∑ i, m i • b.baseSupp i + ∑ i, n i • b.baseSupp i) = 0 at hn'
      simp_rw [LinearMap.coe_zero_iff, ← Finset.sum_add_distrib, ← add_smul, ← Pi.add_apply,
        ← Nat.cast_smul_eq_nsmul R] at hn'
      exact hn'
    have := Fintype.linearIndependent_iff.mp LieAlgebra.Basis.linearIndependent_baseSupp b ((↑) ∘ (m + n)) hn'
    refine hn <| funext fun i ↦ ?_
    specialize this i
    rw [comp_apply, Nat.cast_eq_zero, Pi.add_apply, Nat.add_eq_zero_iff] at this
    simpa using this.2
  have key := LieModule.iSupIndep_genWeightSpace R b.cartan L
  have h₀ : Disjoint (rootSpace b.cartan 0) (U ⊔ V) := by
    convert key.disjoint_biSup_biSup (hU0.union_right hV0)
    rw [iSup_union, hsU', hsV']
  have h₁ : Disjoint U (V ⊔ rootSpace b.cartan 0) := by
    convert key.disjoint_biSup_biSup (hUV.union_right hU0.symm)
    rw [iSup_union, hs0', hsV']
  have h₂ : Disjoint V (rootSpace b.cartan 0 ⊔ U) := by
    convert key.disjoint_biSup_biSup (Disjoint.union_left hV0 hUV).symm
    rw [iSup_union, hs0', hsU']
  simp [iSupIndep_fin_three, h₀, h₁, h₂]

