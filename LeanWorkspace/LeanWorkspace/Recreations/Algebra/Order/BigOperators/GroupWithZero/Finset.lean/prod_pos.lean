import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f g : ι → R}
  {s t : Finset ι}

theorem prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i := prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0

