import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem eval_eq_truncLT [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {c : FiniteArchimedeanClass M} {y : f.val.domain}
    (hy : ArchimedeanClass.mk (y.val - x) = c.val) (h : ∀ z : f.val.domain, z.val - x ∉ ball K c) :
    f.eval x = toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.val y))) := by
  unfold HahnEmbedding.Partial.eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    exact HahnEmbedding.Partial.evalCoeff_eq _ fun _ ↦ by simpa [hy]
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]
    apply HahnEmbedding.Partial.evalCoeff_eq_zero
    contrapose! h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, (ball_strictAnti K).antitone (by simpa using hd) hz⟩

