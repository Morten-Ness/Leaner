import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem zero_or_exists_mk' (x : ValueGroup₀ f) :
    x = 0 ∨ ∃ d : {xy : A × A // f xy.1 ≠ 0 ∧ f xy.2 ≠ 0}, x =
      MonoidWithZeroHom.valueGroup.mk f d.1.1 d.1.2 d.2.1 d.2.2 := ValueGroup₀.zero_or_exists_mk x.imp _root_.id fun ⟨r, s, hr, hs, hx⟩ ↦ ⟨⟨(r, s), ⟨hr, hs⟩⟩, hx⟩

