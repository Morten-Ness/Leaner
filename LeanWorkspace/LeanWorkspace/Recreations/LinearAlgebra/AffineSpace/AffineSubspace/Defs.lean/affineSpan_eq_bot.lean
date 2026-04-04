import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {s : Set P}

theorem affineSpan_eq_bot : affineSpan k s = ⊥ ↔ s = ∅ := by
  rw [← not_iff_not, ← Ne, ← Ne, ← AffineSubspace.nonempty_iff_ne_bot, affineSpan_nonempty,
    nonempty_iff_ne_empty]

