import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem lift_mk {α : Type*} (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), FiniteMulArchimedeanClass.mk a.val a.prop = FiniteMulArchimedeanClass.mk b.val b.prop → f a = f b)
    {a : M} (ha : a ≠ 1) :
    FiniteMulArchimedeanClass.lift f h (FiniteMulArchimedeanClass.mk a ha) = f ⟨a, ha⟩ := by simp [FiniteMulArchimedeanClass.lift, FiniteMulArchimedeanClass.mk, ha]

