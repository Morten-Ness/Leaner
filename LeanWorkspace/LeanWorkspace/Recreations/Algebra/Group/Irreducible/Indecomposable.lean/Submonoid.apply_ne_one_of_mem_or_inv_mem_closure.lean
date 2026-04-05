import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem Submonoid.apply_ne_one_of_mem_or_inv_mem_closure
    [InvolutiveInv ι] [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G)
    (f : G →* S)
    (s : Set ι)
    (hf : ∀ i ∈ s, 1 < f (v i))
    (i : ι) (hv_one : v i ≠ 1) (hv_inv : v i⁻¹ = (v i)⁻¹)
    (hsp : v i ∈ closure (v '' s) ∨ (v i)⁻¹ ∈ closure (v '' s)) :
    f (v i) ≠ 1 := by
  wlog hi : v i ∈ closure (v '' s)
  · rcases hsp with hi' | hi'; · contradiction
    simpa [hv_inv] using this v f s hf i⁻¹ (by simpa [hv_inv]) (by simp [hv_inv])
      (by left; simpa [hv_inv]) (by simpa [hv_inv])
  suffices v i ≠ 1 → 1 < f (v i) from (this hv_one).ne'
  refine closure_induction (by simp_all) (by simp) (fun x y _ _ hx hy _ ↦ ?_) hi
  rcases eq_or_ne x 1 with rfl | hx'; · grind
  rcases eq_or_ne y 1 with rfl | hy'; · grind
  simpa using lt_mul_of_lt_of_one_lt (hx hx') (hy hy')

