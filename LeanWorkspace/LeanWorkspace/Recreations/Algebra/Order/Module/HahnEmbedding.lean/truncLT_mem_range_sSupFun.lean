import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem truncLT_mem_range_sSupFun {c : Set (HahnEmbedding.Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) (x : (HahnEmbedding.Partial.sSupFun hc).domain)
    (c : FiniteArchimedeanClass M) :
    toLex ((HahnSeries.truncLTLinearMap K c) (ofLex (HahnEmbedding.Partial.sSupFun hc x))) ∈
    LinearMap.range (HahnEmbedding.Partial.sSupFun hc).toFun := by
  obtain hx := x.prop
  simp_rw [HahnEmbedding.Partial.sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range) ⟨x, hf⟩ c
  simp_rw [LinearMap.mem_range, LinearPMap.toFun_eq_coe] at ⊢ h
  obtain ⟨x', hx'⟩ := h
  have hmem' : x'.val ∈ (HahnEmbedding.Partial.sSupFun hc).domain := by
    apply Set.mem_of_mem_of_subset x'.prop
    exact hf'.symm ▸ (HahnEmbedding.Partial.le_sSupFun hc hmem').1
  refine ⟨⟨x'.val, hmem'⟩, ?_⟩
  have hleft : HahnEmbedding.Partial.sSupFun hc ⟨x'.val, hmem'⟩ = f x' := LinearPMap.sSup_apply _ hmem _
  have hright : HahnEmbedding.Partial.sSupFun hc x = f ⟨x, hf⟩ := LinearPMap.sSup_apply _ hmem ⟨x, hf⟩
  simpa [hleft, hright] using hx'

