import Mathlib

variable {ι α β M N G k R : Type*}

variable [Fintype ι] [CommMonoid M] [Preorder M] [MulLeftMono M] {f : ι → M}

theorem prod_eq_one_iff_of_one_le {ι M : Type*} [Fintype ι] [CommMonoid M] [PartialOrder M]
    [MulLeftMono M] {f : ι → M} (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 := (Finset.prod_eq_one_iff_of_one_le' fun i _ ↦ hf i).trans <| by simp [funext_iff]

