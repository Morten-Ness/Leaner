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


theorem stdPart_eq_zero {x : K} : ArchimedeanClass.stdPart x = 0 ↔ ArchimedeanClass.mk x ≠ 0 where
  mpr h := by
    obtain h | h := h.lt_or_gt
    · exact dif_neg h.not_ge
    · rw [ArchimedeanClass.stdPart, dif_pos h.le, OrderRingHom.comp_apply, ArchimedeanClass.FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [ArchimedeanClass.stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, ArchimedeanClass.FiniteResidueField.mk_ne_zero]

alias ⟨_, stdPart_of_mk_ne_zero⟩ := stdPart_eq_zero

