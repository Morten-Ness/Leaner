import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

include hS in
theorem span_exact {β : Type*} {u : ι ⊕ β → S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
    (hv : ⊤ ≤ span R (Set.range v))
    (hw : ⊤ ≤ span R (Set.range (S.g ∘ u ∘ Sum.inr))) :
    ⊤ ≤ span R (Set.range u) := by
  intro m _
  have hgm : S.g m ∈ span R (Set.range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j))
  have hsub : m - m' ∈ LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsuppSum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ span R (Set.range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsuppSum] at hnm
  rw [← sub_add_cancel m m', ← hnm]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • S.f (v a)) =
      (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

