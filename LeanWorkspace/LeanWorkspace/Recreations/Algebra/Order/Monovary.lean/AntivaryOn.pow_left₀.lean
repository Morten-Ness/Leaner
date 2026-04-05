import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem AntivaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _

