import Mathlib

variable {α : Type*}

variable [Zero α]

theorem coe_untop₀_of_ne_top {a : WithTop α} (ha : a ≠ ⊤) :
    a.untop₀ = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

