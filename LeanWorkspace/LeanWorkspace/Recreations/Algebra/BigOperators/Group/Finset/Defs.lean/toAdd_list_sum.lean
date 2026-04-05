import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [AddMonoid M]

set_option backward.isDefEq.respectTransparency false in
theorem toAdd_list_sum (s : List (Multiplicative M)) : s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

