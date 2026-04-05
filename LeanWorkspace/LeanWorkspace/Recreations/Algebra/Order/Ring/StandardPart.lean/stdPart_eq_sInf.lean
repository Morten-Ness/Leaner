import Mathlib

private theorem ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (ArchimedeanClass.FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa


private theorem mul_le_mul_of_nonneg_left' {x y z : ArchimedeanClass.FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
    z * x ≤ z * y := by
  induction x with | ArchimedeanClass.FiniteResidueField.mk x
  induction y with | ArchimedeanClass.FiniteResidueField.mk y
  induction z with | ArchimedeanClass.FiniteResidueField.mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero ArchimedeanClass.FiniteResidueField.mk] at hz
  rw [ArchimedeanClass.FiniteResidueField.mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]


theorem stdPart_eq_sInf (f : ℝ →+*o K) (x : K) : ArchimedeanClass.stdPart x = sInf {r | x < f r} := by
  obtain hx | hx := le_or_gt 0 (ArchimedeanClass.mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr ↦ ?_⟩
      by_contra! hra
      exact (f.monotone' hra.le).not_gt (by simpa using ha.trans hr)
    apply ArchimedeanClass.stdPart_eq f <;> intro r hr
    · simpa using notMem_of_lt_csInf hr hb
    · obtain ⟨s, hs, hs'⟩ := (csInf_lt_iff hb hn).1 hr
      exact hs.le.trans (f.monotone' hs'.le)
  · rw [stdPart_of_mk_ne_zero hx.ne]
    have hr {r} := hx.trans_le (mk_map_nonneg_of_archimedean f r)
    obtain h | h := le_or_gt 0 x
    · convert Real.sInf_empty.symm
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun r ↦ (lt_of_mk_lt_mk_of_nonneg hr h).not_gt
    · convert Real.sInf_univ.symm
      rw [Set.eq_univ_iff_forall]
      exact fun r ↦ lt_of_mk_lt_mk_of_nonpos hr h.le

