import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem IsOrdering.mk' [HasMemOrNegMem P]
    (h : ∀ {x y}, x * y ∈ P.support → x ∈ P.support ∨ y ∈ P.support) : P.IsOrdering where
  ne_top' := RingPreordering.support_ne_top P
  mem_or_mem' := h

