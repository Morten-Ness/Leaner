import Mathlib

section

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1)
    (s : Set ι) (hst : s ⊆ {j | IsMulIndecomposable v {i | 1 < f (v i)} j}) :
    s.Pairwise fun i j ↦ v i / v j ∉ Set.range v := by
  have hv_one : ∀ i, v i ≠ 1 := fun i ↦ by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply IsMulIndecomposable.pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i ↦ ?_
  simpa [hv_inv] using (hf i).symm

end

section

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_div_notMem_range [InvolutiveInv ι]
    (v : ι → G)
    (hv_one : ∀ i, v i ≠ 1)
    (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (s t : Set ι)
    (hst : s ⊆ {i | IsMulIndecomposable v t i})
    (hv_t : ∀ i, i ∈ t ∨ i⁻¹ ∈ t) :
    s.Pairwise fun i j ↦ v i / v j ∉ Set.range v := by
  have h_sub : s ⊆ t := hst.trans (IsMulIndecomposable.subset _ _)
  intro i hi j hj hne
  by_contra! ⟨k, hk⟩
  rcases hv_t k with hk' | hk'
  · suffices ¬ IsMulIndecomposable v t i from this (hst hi)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ ↦ ⟨k, hk', j, h_sub hj, by simp [hk]⟩
  · suffices ¬ IsMulIndecomposable v t j from this (hst hj)
    simp only [IsMulIndecomposable, hv_one, or_self, imp_false, not_and, not_forall, not_not]
    exact fun _ ↦ ⟨k⁻¹, hk', i, h_sub hi, by simp [hv_inv, hk]⟩

end
