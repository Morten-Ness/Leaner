import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.comm_left {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₂, p₁, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 1)]
  convert h using 1
  ext x
  fin_cases x <;> rfl

