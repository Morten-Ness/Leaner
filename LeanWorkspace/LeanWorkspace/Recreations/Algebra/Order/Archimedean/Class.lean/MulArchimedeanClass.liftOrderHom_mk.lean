import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {α : Type*} [PartialOrder α]

theorem liftOrderHom_mk (f : M → α) (h : ∀ a b, MulArchimedeanClass.mk a ≤ MulArchimedeanClass.mk b → f a ≤ f b) (a : M) :
    MulArchimedeanClass.liftOrderHom f h (MulArchimedeanClass.mk a) = f a := MulArchimedeanClass.lift_mk f (fun a b heq ↦ le_antisymm (h a b heq.le) (h b a heq.ge)) a

