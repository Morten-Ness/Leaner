import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem Submonoid.mem_closure_image_one_lt_iff [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι → M) (f : M →* S) (i : ι) (hv_one : v i ≠ 1) :
    v i ∈ closure (v '' {i | 1 < f (v i)}) ↔ 1 < f (v i) := by
  refine ⟨fun hi ↦ ?_, fun hi ↦ subset_closure <| mem_image_of_mem v hi⟩
  suffices v i = 1 ∨ 1 < f (v i) from this.resolve_left hv_one
  refine closure_induction (by grind) (by simp) (fun x y _ _ hx hy ↦ ?_) hi
  rcases hx with rfl | hx; · simpa
  rcases hy with rfl | hy; · right; simpa
  right
  simpa only [map_mul] using Left.one_lt_mul hx hy

