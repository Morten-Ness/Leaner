import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem IsMulIndecomposable.apply_ne_one_iff_mem_closure
    [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (f : G →* S) (i : ι) (hi : v i ≠ 1) (hi' : v i⁻¹ = (v i)⁻¹) :
    f (v i) ≠ 1 ↔ v i ∈ closure (v '' baseOf v f) ∨ (v i)⁻¹ ∈ closure (v '' baseOf v f) := ⟨fun h ↦ IsMulIndecomposable.mem_or_inv_mem_closure_baseOf v f i h hi',
    apply_ne_one_of_mem_or_inv_mem_closure v f (baseOf v f) (baseOf_subset_one_lt v f) i hi hi'⟩

