import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

include hv hm in
theorem linearIndependent_leftExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g.hom hw, ModuleCat.disjoint_span_sum hS hw huv⟩
  rw [huv, LinearMap.linearIndependent_iff S.f.hom]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv

