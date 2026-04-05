import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

