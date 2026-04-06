FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem nonempty_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) : s.Nonempty := by
  by_contra hs
  rw [Set.not_nonempty_iff_eq_empty] at hs
  subst hs
  have h' : (⊥ : Submodule k V) = ⊤ := by
    simpa using congrArg AffineSubspace.direction h
  exact Submodule.bot_ne_top h'
