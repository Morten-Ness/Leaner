import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem bot_ne_top : (⊥ : AffineSubspace k P) ≠ ⊤ := by
  intro contra
  rw [AffineSubspace.ext_iff, AffineSubspace.bot_coe, AffineSubspace.top_coe] at contra
  exact Set.empty_ne_univ contra

instance : Nontrivial (AffineSubspace k P) :=
  ⟨⟨⊥, ⊤, bot_ne_top k V P⟩⟩

