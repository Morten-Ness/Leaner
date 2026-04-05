import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem eval_smul [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M) :
    f.eval (k • x) = k • f.eval x := by
  by_cases hk : k = 0
  · simp [hk]
  unfold HahnEmbedding.Partial.eval
  rw [← toLex_smul, toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - k • x = k • (y.val - x) := by simp [smul_sub]
    have hy' : (k • y).val - k • x ∈ ball K c := by
      rw [heq]
      exact Submodule.smul_mem _ _ hy
    simp [HahnEmbedding.Partial.evalCoeff_eq f hy, HahnEmbedding.Partial.evalCoeff_eq f hy', LinearPMap.map_smul]
  have h' : ¬∃ y : f.val.domain, y.val - k • x ∈ ball K c := by
    contrapose! h
    obtain ⟨y, hy⟩ := h
    use k⁻¹ • y
    have heq : (k⁻¹ • y).val - x = k⁻¹ • (y.val - k • x) := by
      simp [smul_sub, smul_smul, inv_mul_cancel₀ hk]
    exact heq ▸ Submodule.smul_mem _ _ hy
  simp [HahnEmbedding.Partial.evalCoeff_eq_zero f h, HahnEmbedding.Partial.evalCoeff_eq_zero f h']

