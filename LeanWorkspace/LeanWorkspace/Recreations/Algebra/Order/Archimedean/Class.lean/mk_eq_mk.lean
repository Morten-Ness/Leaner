import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

set_option backward.isDefEq.respectTransparency false in
theorem mk_eq_mk {a b : M} : MulArchimedeanClass.mk a = MulArchimedeanClass.mk b ↔ (∃ m, |b|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, |a|ₘ ≤ |b|ₘ ^ n) := by
  unfold MulArchimedeanClass.mk toAntisymmetrization
  rw [Quotient.eq]
  rfl

