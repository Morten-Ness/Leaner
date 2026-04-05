import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1)
    (s : Set ι) (hst : s ⊆ {j | IsMulIndecomposable v {i | 1 < f (v i)} j}) :
    s.Pairwise fun i j ↦ v i / v j ∉ Set.range v := by
  have hv_one : ∀ i, v i ≠ 1 := fun i ↦ by contrapose! hf; exact ⟨i, by simp [hf]⟩
  apply IsMulIndecomposable.pairwise_div_notMem_range v hv_one hv_inv s {i | 1 < f (v i)} hst fun i ↦ ?_
  simpa [hv_inv] using (hf i).symm

