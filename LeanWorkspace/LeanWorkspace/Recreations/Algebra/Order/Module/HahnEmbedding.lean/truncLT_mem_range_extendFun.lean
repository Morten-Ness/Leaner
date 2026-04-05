import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem truncLT_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.extendFun hx y))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  obtain ⟨y', hy'⟩ := y
  rw [HahnEmbedding.Partial.extendFun, LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [HahnEmbedding.Partial.extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw [ofLex_add, map_add, toLex_add, ofLex_smul, map_smul, toLex_smul]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · obtain ⟨⟨a', ha'mem⟩, ha'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range ⟨a, ha⟩ c)
    refine LinearMap.mem_range.mpr ⟨⟨a', by simpa using Submodule.mem_sup_left ha'mem⟩, ?_⟩
    rw [← ha']
    exact LinearPMap.supSpanSingleton_apply_mk_of_mem f.val _ hx ha'mem
  · apply HahnEmbedding.Partial.truncLT_eval_mem_range_extendFun

