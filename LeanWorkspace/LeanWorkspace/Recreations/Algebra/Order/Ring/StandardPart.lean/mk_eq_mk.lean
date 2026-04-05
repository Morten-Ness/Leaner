import Mathlib

private theorem ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (ArchimedeanClass.FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa


set_option backward.isDefEq.respectTransparency false in
theorem mk_eq_mk {x y : ArchimedeanClass.FiniteElement K} : ArchimedeanClass.FiniteResidueField.mk x = ArchimedeanClass.FiniteResidueField.mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]

