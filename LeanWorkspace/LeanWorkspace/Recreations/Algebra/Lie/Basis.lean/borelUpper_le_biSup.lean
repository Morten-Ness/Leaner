import Mathlib

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

variable [Fintype ι]

variable [IsDomain R] [CharZero R]

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


theorem borelUpper_le_biSup :
    b.borelUpper ≤ ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace b.cartan (∑ i, n i • b.baseSupp i) := by
  classical
  intro x hx
  replace hx : x ∈ lieSpan R L (Set.range b.e) := by simpa [LieAlgebra.Basis.borelUpper] using hx
  induction hx using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    apply LieSubmodule.mem_iSup_of_mem (Pi.single i 1)
    simp only [ne_eq, Pi.single_eq_zero_iff, one_ne_zero, not_false_eq_true, nsmul_eq_mul, iSup_pos,
      LieModule.mem_genWeightSpace, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
      Subtype.forall, toEnd_mk]
    exact fun y hy ↦ ⟨1, by simp [Pi.single_apply]⟩
  | zero => simp
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    let s : Set (b.cartan → R) := {χ | ∃ n : ι → ℕ, n ≠ 0 ∧ χ = ∑ i, n i • b.baseSupp i}
    have hs : ∀ χ₁ ∈ s, ∀ χ₂ ∈ s, χ₁ + χ₂ ∈ s := by
      rintro - ⟨n₁, hn₁, rfl⟩ - ⟨n₂, hn₂, rfl⟩
      refine ⟨n₁ + n₂, by simp [hn₁], ?_⟩
      ext; simp [add_smul, Finset.sum_add_distrib]
    let e : {n : ι → ℕ | n ≠ 0} ≃ s :=
      .ofBijective (fun n ↦ ⟨∑ i, n.val i • b.baseSupp i, n.val, n.property, by ext; simp⟩) <| by
      refine ⟨fun n₁ n₂ h ↦ ?_, fun χ ↦ ?_⟩
      · ext i
        have := LieAlgebra.Basis.linearIndependent_baseSupp b.restrict_scalars' ℕ
        refine Fintype.linearIndependent_iffₛ.mp this n₁ n₂ ?_ i
        ext v
        rw [Subtype.mk.injEq] at h
        simpa using congr_fun h v
      · use ⟨χ.property.choose, χ.property.choose_spec.1⟩
        ext i
        simpa using congr_fun χ.property.choose_spec.2.symm i
    replace hu : u ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace b.cartan χ := by
      convert hu; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    replace hv : v ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace b.cartan χ := by
      convert hv; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    convert mem_biSup_genWeightSpace_of hs hu hv
    rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl

