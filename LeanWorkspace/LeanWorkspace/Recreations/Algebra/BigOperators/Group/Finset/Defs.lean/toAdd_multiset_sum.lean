import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [AddCommMonoid M]

set_option backward.isDefEq.respectTransparency false in
theorem toAdd_multiset_sum (s : Multiset (Multiplicative M)) :
    s.prod.toAdd = (s.map toAdd).sum := by
  simp [toAdd, ofAdd]; rfl

