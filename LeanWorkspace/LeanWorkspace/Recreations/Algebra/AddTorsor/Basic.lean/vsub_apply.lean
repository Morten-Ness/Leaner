import Mathlib

open scoped Pointwise

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}
  [∀ i, AddTorsor (fg i) (fp i)]

theorem vsub_apply (p q : ∀ i, fp i) (i : I) : (p -ᵥ q) i = p i -ᵥ q i := rfl

