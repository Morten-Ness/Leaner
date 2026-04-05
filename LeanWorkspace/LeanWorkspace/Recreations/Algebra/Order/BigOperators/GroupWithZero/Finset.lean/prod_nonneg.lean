import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i := prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0

