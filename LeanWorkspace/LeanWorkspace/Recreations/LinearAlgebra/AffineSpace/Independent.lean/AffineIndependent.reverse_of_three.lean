import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.reverse_of_three {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₃, p₂, p₁] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 2)]
  convert h using 1
  ext x
  fin_cases x <;> rfl

