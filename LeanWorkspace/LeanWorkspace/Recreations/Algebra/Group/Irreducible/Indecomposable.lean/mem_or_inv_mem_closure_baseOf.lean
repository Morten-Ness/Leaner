import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem mem_or_inv_mem_closure_baseOf [Finite ι] [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G)
    (f : G →* S) (i : ι) (hi : f (v i) ≠ 1) (hi' : v i⁻¹ = (v i)⁻¹) :
     v i    ∈ Submonoid.closure (v '' baseOf v f) ∨
    (v i)⁻¹ ∈ Submonoid.closure (v '' baseOf v f) := by
  rw [Submonoid.closure_image_isMulIndecomposable_baseOf v f]
  rcases lt_or_gt_of_ne hi with hj | hj
  · right
    exact Submonoid.subset_closure ⟨i⁻¹, by simpa [hi']⟩
  · left
    exact Submonoid.subset_closure ⟨i, by simpa⟩

