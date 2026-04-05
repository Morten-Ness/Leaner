import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g Units.ne_zero g := Iff.trans (by simp_rw [Units.val_mk0]) Units.exists0.symm

