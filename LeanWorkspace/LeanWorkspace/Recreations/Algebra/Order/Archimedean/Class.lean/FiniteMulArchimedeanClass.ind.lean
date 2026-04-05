import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem ind {motive : FiniteMulArchimedeanClass M → Prop}
    (FiniteMulArchimedeanClass.mk : ∀ a, (ha : a ≠ 1) → motive (.mk a ha)) : ∀ x, motive x := by
  simpa [FiniteMulArchimedeanClass, MulArchimedeanClass.forall]

