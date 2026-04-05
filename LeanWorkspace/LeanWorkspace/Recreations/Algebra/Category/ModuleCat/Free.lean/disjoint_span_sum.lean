import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

theorem disjoint_span_sum : Disjoint (span R (Set.range (u ∘ Sum.inl)))
    (span R (Set.range (u ∘ Sum.inr))) := by
  rw [huv, disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.coe_range, span_eq (LinearMap.range S.f.hom), hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw

