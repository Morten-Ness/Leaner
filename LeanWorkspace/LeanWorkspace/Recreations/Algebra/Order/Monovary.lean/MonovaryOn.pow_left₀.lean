import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem MonovaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _

