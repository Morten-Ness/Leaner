import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [AddCommMonoid M]

set_option backward.isDefEq.respectTransparency false in
theorem ofAdd_multiset_prod (s : Multiset M) : ofAdd s.sum = (s.map ofAdd).prod := by
  simp [ofAdd]; rfl

