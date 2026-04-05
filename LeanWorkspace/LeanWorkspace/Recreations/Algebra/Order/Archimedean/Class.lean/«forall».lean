import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem «forall» {p : MulArchimedeanClass M → Prop} : (∀ A, p A) ↔ ∀ a, p (MulArchimedeanClass.mk a) := Quotient.forall

