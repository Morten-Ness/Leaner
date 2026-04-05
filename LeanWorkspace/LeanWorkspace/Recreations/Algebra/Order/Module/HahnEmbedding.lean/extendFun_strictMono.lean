import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem extendFun_strictMono [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : StrictMono (f.extendFun hx) := by
  have hx' {c : K} (hc : c ≠ 0) : -c • x ∉ f.val.domain := by
    contrapose! hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyzmem := (z - y).prop
  nth_rw 1 [HahnEmbedding.Partial.extendFun, LinearPMap.domain_supSpanSingleton] at hyzmem
  -- decompose `v = a + c • x`, reducing this to HahnEmbedding.Partial.eval_lt
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyzmem
  have : z - y = ⟨a + b, hab.symm ▸ (z - y).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hyz
  have habpos : 0 < a + b := by exact hyz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hc] at habpos
  simp_rw [← hc, HahnEmbedding.Partial.extendFun]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]
  suffices f.eval (-c • x) < f.val ⟨a, ha⟩ by
    rw [HahnEmbedding.Partial.eval_smul, neg_smul] at this
    exact neg_lt_iff_pos_add.mp this
  have hac : -c • x < a := by
    rw [neg_smul]
    exact neg_lt_iff_pos_add.mpr habpos
  by_cases hc : c = 0
  · rw [hc] at ⊢ hac
    suffices f.val 0 < f.val ⟨a, ha⟩ by simpa using this
    exact f.prop.strictMono (by simpa using hac)
  · exact HahnEmbedding.Partial.eval_lt f (hx' hc) ⟨a, ha⟩ hac

