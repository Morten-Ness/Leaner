import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

set_option backward.isDefEq.respectTransparency false in
theorem ofMul_multiset_prod (s : Multiset M) : ofMul s.prod = (s.map ofMul).sum := by
  simp [ofMul]; rfl

