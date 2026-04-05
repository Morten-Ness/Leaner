import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]

variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem of_rightInvOn (h₁ : Function.LeftInverse f (algebraMap R S))
    (h₂ : (spectrum S a).RightInvOn f (algebraMap R S)) : SpectrumRestricts a f where
  SpectrumRestricts.rightInvOn x hx := by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁

