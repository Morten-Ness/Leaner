import Mathlib

open scoped Pointwise

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}
  [∀ i, AddTorsor (fg i) (fp i)]

theorem vsub_def (p q : ∀ i, fp i) : p -ᵥ q = fun i => p i -ᵥ q i := rfl

