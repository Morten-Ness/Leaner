import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem lift₂_mk {α : Type*} (f : M → M → α)
    (h : ∀ a₁ b₁ a₂ b₂, MulArchimedeanClass.mk a₁ = MulArchimedeanClass.mk b₁ → MulArchimedeanClass.mk a₂ = MulArchimedeanClass.mk b₂ → f a₁ a₂ = f b₁ b₂)
    (a b : M) : MulArchimedeanClass.lift₂ f h (MulArchimedeanClass.mk a) (MulArchimedeanClass.mk b) = f a b := by
  unfold MulArchimedeanClass.lift₂
  exact Quotient.lift₂_mk f (fun _ _ _ _ h₁ h₂ ↦ h _ _ _ _ (MulArchimedeanClass.mk_eq_mk.mpr h₁) (MulArchimedeanClass.mk_eq_mk.mpr h₂)) a b

