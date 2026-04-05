import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

theorem liftOrderHom_mk {α : Type*} [PartialOrder α]
    (f : {a : M // a ≠ 1} → α)
    (h : ∀ (a b : {a : M // a ≠ 1}), FiniteMulArchimedeanClass.mk a.val a.prop ≤ FiniteMulArchimedeanClass.mk b.val b.prop → f a ≤ f b)
    {a : M} (ha : a ≠ 1) : FiniteMulArchimedeanClass.liftOrderHom f h (FiniteMulArchimedeanClass.mk a ha) = f ⟨a, ha⟩ := FiniteMulArchimedeanClass.lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) ha

