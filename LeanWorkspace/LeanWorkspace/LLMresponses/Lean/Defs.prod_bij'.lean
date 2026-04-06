import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  refine Finset.prod_bij' i j hi hj left_inv right_inv ?_
  intro a ha
  simpa [h a ha]
