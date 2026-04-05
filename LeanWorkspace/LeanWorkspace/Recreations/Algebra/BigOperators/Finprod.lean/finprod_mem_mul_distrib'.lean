import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_mul_distrib' (hf : (s ∩ mulSupport f).Finite) (hg : (s ∩ mulSupport g).Finite) :
    ∏ᶠ i ∈ s, f i * g i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i := by
  rw [← mulSupport_mulIndicator] at hf hg
  simp only [finprod_mem_def, mulIndicator_mul, finprod_mul_distrib hf hg]

