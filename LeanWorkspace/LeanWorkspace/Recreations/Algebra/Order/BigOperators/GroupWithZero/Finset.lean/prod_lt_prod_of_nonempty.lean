import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [PartialOrder R] [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f g : ι → R}
  {s t : Finset ι}

theorem prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply Finset.prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

