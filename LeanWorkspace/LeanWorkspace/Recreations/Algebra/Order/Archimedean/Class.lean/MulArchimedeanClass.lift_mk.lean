import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem lift_mk {α : Type*} (f : M → α) (h : ∀ a b, MulArchimedeanClass.mk a = MulArchimedeanClass.mk b → f a = f b)
    (a : M) : MulArchimedeanClass.lift f h (MulArchimedeanClass.mk a) = f a := by
  unfold MulArchimedeanClass.lift
  exact Quotient.lift_mk f (fun _ _ h' ↦ h _ _ <| MulArchimedeanClass.mk_eq_mk.mpr h') a

