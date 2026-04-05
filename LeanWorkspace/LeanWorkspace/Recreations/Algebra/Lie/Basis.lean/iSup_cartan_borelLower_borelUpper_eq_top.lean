import Mathlib

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L] (b : Basis ι R L)

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


theorem iSup_cartan_borelLower_borelUpper_eq_top :
    iSup ![b.cartan.toLieSubmodule, b.borelLower, b.borelUpper] = ⊤ := by
  suffices b.cartan.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx ↦ ?_
  replace hx : x ∈ lieSpan R L (Set.range b.e ∪ Set.range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu | hu
    · exact LieSubmodule.mem_sup_right <| subset_lieSpan hu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| subset_lieSpan hu
  | zero => simp
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul t u _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    obtain ⟨yc, hyc, yl, hyl, yu, hyu, rfl⟩ :
        ∃ᵉ (yc ∈ b.cartan) (yl ∈ lieSpan R L (Set.range b.f)) (yu ∈ lieSpan R L (Set.range b.e)),
          yc + yl + yu = u := by simpa [LieSubmodule.mem_sup] using hu
    obtain ⟨zc, hzc, zl, hzl, zu, hzu, rfl⟩ :
        ∃ᵉ (zc ∈ b.cartan) (zl ∈ lieSpan R L (Set.range b.f)) (zu ∈ lieSpan R L (Set.range b.e)),
          zc + zl + zu = v := by simpa [LieSubmodule.mem_sup] using hv
    simp only [lie_add, add_lie, ← add_assoc]
    repeat apply add_mem
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_left <| lie_mem _ hyc hzc
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨zc, hzc⟩) hyl
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨zc, hzc⟩) hyu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨yc, hyc⟩) hzl
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| lie_mem _ hyl hzl
    · exact iSup_cartan_borelLower_borelUpper_eq_top_aux b hyu hzl
    · exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hzu
    · rw [← lie_skew, neg_mem_iff]
      exact iSup_cartan_borelLower_borelUpper_eq_top_aux b hzu hyl
    · exact LieSubmodule.mem_sup_right <| lie_mem _ hyu hzu

