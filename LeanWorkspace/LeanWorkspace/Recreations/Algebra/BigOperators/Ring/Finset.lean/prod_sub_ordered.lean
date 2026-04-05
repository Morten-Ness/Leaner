import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j - g j)) * ∏ j ∈ s with i < j, f j := by
  simp only [sub_eq_add_neg]
  convert Finset.prod_add_ordered s f fun i => -g i
  simp

