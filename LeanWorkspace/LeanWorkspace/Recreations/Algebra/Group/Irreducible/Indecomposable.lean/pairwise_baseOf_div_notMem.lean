import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem pairwise_baseOf_div_notMem [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1) :
    (baseOf v f).Pairwise fun i j ↦ v i / v j ∉ Set.range v := IsMulIndecomposable.pairwise_div_notMem_range' v hv_inv f hf (baseOf v f) (.refl _)

set_option linter.style.whitespace false in -- manual alignment is not recognised

