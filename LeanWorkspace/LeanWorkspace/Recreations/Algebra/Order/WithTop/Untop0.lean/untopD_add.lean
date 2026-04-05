import Mathlib

variable {α : Type*}

theorem untopD_add [Add α] {a b : WithTop α} {c : α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untopD c = a.untopD c + b.untopD c := by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

