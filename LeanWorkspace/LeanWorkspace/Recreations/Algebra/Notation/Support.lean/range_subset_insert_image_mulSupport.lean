import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem range_subset_insert_image_mulSupport (f : ι → M) :
    Set.range f ⊆ insert 1 (f '' Function.mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using
    fun x (hx : x ∈ Function.mulSupport f) ↦ mem_image_of_mem f hx

