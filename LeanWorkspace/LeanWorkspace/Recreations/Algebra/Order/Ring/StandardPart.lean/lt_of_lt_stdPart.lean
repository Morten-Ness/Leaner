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


theorem lt_of_lt_stdPart (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ ArchimedeanClass.mk x) (h : r < ArchimedeanClass.stdPart x) : f r < x := by
  rw [← sub_lt_sub_iff_right (c := f (ArchimedeanClass.stdPart x)), ← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', ArchimedeanClass.mk_sub_pos_iff f hx]
    rw [ne_eq, sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

