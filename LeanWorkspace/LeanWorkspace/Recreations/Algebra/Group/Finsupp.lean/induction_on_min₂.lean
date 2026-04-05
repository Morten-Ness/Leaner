import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

variable [LinearOrder ι] {motive : (ι →₀ M) → Prop}

theorem induction_on_min₂ (f : ι →₀ M) (zero : motive 0)
    (add_single : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 →
      motive f → motive (f + single a b)) : motive f := Finsupp.induction_on_max₂ (ι := ιᵒᵈ) f zero add_single

