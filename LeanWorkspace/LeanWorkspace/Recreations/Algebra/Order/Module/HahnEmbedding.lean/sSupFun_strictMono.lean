import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem sSupFun_strictMono [IsOrderedAddMonoid R] {c : Set (HahnEmbedding.Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : StrictMono (HahnEmbedding.Partial.sSupFun hc) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [HahnEmbedding.Partial.sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (HahnEmbedding.Partial.sSupFun hc) (y - x) = f ⟨(y - x).val, hf⟩ :=
    LinearPMap.sSup_apply _ hmem ⟨(y - x).val, hf⟩
  rw [this]
  obtain ⟨f', _, hf'⟩ := (Set.mem_image _ _ _).mp hmem
  have hmono : StrictMono f := hf'.symm ▸ f'.prop.strictMono
  rw [show 0 = f 0 by simp]
  apply hmono
  rw [← Subtype.coe_lt_coe]
  simp [h]

