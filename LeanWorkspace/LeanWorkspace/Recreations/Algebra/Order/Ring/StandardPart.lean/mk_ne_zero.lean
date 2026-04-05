import Mathlib

private theorem ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (ArchimedeanClass.FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa


theorem mk_ne_zero {x : ArchimedeanClass.FiniteElement K} : ArchimedeanClass.FiniteResidueField.mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, ArchimedeanClass.FiniteResidueField.mk_eq_zero, not_lt, x.2.ge_iff_eq']

