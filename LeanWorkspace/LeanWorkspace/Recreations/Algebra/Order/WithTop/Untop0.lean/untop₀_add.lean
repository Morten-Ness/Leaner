import Mathlib

variable {α : Type*}

theorem untop₀_add [AddZeroClass α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop₀ = a.untop₀ + b.untop₀ := WithTop.untopD_add ha hb

