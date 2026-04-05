import Mathlib

variable {R : Type*}

theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

