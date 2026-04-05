import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [Preorder M] [MulLeftMono M] {f : ι → M}

theorem one_le_prod (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod' fun _ _ ↦ hf _

