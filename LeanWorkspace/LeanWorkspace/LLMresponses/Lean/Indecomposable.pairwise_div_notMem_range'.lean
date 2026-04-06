import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_div_notMem_range' [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1)
    (s : Set ι) (hst : s ⊆ {j | IsMulIndecomposable v {i | 1 < f (v i)} j}) :
    s.Pairwise fun i j ↦ v i / v j ∉ Set.range v := by
  simpa using
    IsMulIndecomposable.pairwise_div_notMem_range' (v := v) (hv_inv := hv_inv)
      (f := f) (hf := hf) (s := s) hst
