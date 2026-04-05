import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Monoid M]

set_option backward.isDefEq.respectTransparency false in
theorem ofMul_list_prod (s : List M) : ofMul s.prod = (s.map ofMul).sum := by simp [ofMul]; rfl

