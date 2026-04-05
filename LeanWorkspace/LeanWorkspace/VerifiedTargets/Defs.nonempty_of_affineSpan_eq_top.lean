import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [AffineSubspace.span_empty] at h
  exact AffineSubspace.bot_ne_top k V P h

