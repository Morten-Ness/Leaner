import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addEquiv_trans (e₁ : M ≃+ N) (e₂ : N ≃+ O) :
    Finsupp.mapRange.addEquiv (ι := ι) (e₁.trans e₂) =
      (Finsupp.mapRange.addEquiv e₁).trans (Finsupp.mapRange.addEquiv e₂) := by ext; simp

