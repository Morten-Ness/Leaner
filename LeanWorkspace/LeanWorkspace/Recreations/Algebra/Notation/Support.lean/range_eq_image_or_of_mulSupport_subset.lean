import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem range_eq_image_or_of_mulSupport_subset {k : Set ι} (h : Function.mulSupport f ⊆ k) :
    Set.range f = f '' k ∨ Set.range f = insert 1 (f '' k) := by
  have : Set.range f ⊆ insert 1 (f '' k) :=
    (Function.range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

