import Mathlib

open scoped Ring

variable {R : Type u}

theorem Pi.star_mulSingle {ι : Type*} {R : ι → Type*} [DecidableEq ι] [∀ i, MulOneClass (R i)]
    [∀ i, StarMul (R i)] (i : ι) (r : R i) : star (mulSingle i r) = mulSingle i (star r) := by
  ext; exact apply_mulSingle (fun _ ↦ star) (fun _ ↦ star_one _) ..

