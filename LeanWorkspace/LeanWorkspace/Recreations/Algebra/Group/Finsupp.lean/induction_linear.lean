import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem induction_linear {motive : (ι →₀ M) → Prop} (f : ι →₀ M) (zero : motive 0)
    (add : ∀ f g : ι →₀ M, motive f → motive g → motive (f + g))
    (single : ∀ a b, motive (single a b)) : motive f := Finsupp.induction₂ f zero fun _a _b _f _ _ w => add _ _ w (single _ _)

