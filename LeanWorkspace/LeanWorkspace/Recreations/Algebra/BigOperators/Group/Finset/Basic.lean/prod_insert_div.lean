import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommGroup G] [DecidableEq ι] {f : ι → G}

theorem prod_insert_div (ha : a ∉ s) (f : ι → G) :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by simp [ha]

