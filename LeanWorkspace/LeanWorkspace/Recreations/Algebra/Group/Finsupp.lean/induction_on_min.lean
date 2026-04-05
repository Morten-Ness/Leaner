import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

variable [LinearOrder ι] {motive : (ι →₀ M) → Prop}

theorem induction_on_min (f : ι →₀ M) (zero : motive 0)
    (Finsupp.single_add : ∀ a b (f : ι →₀ M), (∀ c ∈ f.support, a < c) → b ≠ 0 →
      motive f → motive (single a b + f)) : motive f := Finsupp.induction_on_max (ι := ιᵒᵈ) f zero Finsupp.single_add

