import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

set_option backward.isDefEq.respectTransparency false in
theorem toMul_multiset_sum (s : Multiset (Additive M)) : s.sum.toMul = (s.map toMul).prod := by
  simp [toMul, ofMul]; rfl

