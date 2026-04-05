import Mathlib

variable {a b c p q : ℚ}

theorem _root_.NNRatCast.toOfScientific_def {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      NNRat.cast ⟨(OfScientific.ofScientific m b d : ℚ), Rat.ofScientific_nonneg m b d⟩ := rfl

