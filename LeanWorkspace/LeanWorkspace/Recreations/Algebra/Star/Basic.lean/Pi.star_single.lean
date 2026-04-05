import Mathlib

open scoped Ring

variable {R : Type u}

theorem Pi.star_single {ι : Type*} {R : ι → Type*} [DecidableEq ι] [∀ i, AddMonoid (R i)]
    [∀ i, StarAddMonoid (R i)] (i : ι) (r : R i) : star (single i r) = single i (star r) := by
  ext; exact apply_single (fun _ ↦ star) (fun _ ↦ star_zero _) ..

