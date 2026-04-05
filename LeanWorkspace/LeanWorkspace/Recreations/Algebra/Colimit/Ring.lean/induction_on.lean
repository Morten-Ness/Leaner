import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : Ring.DirectLimit G f → Prop}
    (z : Ring.DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z := let ⟨i, x, hx⟩ := Ring.DirectLimit.exists_of z
  hx ▸ ih i x

