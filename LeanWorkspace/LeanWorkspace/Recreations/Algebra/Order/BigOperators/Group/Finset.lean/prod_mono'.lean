import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [Preorder M] [MulLeftMono M] {f : ι → M}

theorem prod_mono' : Monotone fun f : ι → M ↦ ∏ i, f i := fun _ _ hfg ↦
  Finset.prod_le_prod' fun x _ ↦ hfg x

