import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

set_option backward.isDefEq.respectTransparency false in
theorem truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain)
    (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseEmbedding x))) ∈
    LinearMap.range seed.baseEmbedding.toFun := by
  -- decompose `x` to `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [HahnEmbedding.Seed.domain_baseEmbedding seed] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f' : Π₀ (i : FiniteArchimedeanClass M), seed.stratum i :=
    DFinsupp.mk f.support fun d ↦ if c.val ≤ d.val then 0 else f d.val
  refine ⟨⟨f'.sum fun d x ↦ x.val, ?_⟩, ?_⟩
  · rw [HahnEmbedding.Seed.domain_baseEmbedding seed, ArchimedeanStrata.baseDomain,
      Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  apply_fun ofLex
  rw [ofLex_toLex, LinearPMap.toFun_eq_coe]
  ext d
  rw [HahnEmbedding.Seed.coeff_baseEmbedding seed rfl]
  unfold f'
  obtain hdc | hdc := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc,
      HahnEmbedding.Seed.coeff_baseEmbedding seed hf.symm]
    apply congrArg
    have hcd : ¬ c.val ≤ d.val := not_le_of_gt hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    aesop
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
    have hcd : c.val ≤ d.val := hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    convert LinearMap.map_zero _
    simp

