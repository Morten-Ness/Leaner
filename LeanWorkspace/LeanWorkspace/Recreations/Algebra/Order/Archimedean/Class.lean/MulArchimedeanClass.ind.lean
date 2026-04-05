import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem ind {motive : MulArchimedeanClass M → Prop} (MulArchimedeanClass.mk : ∀ a, motive (.mk a)) : ∀ x, motive x := Antisymmetrization.ind _ MulArchimedeanClass.mk

