import Mathlib

variable {α β : Type*}

theorem Function.Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Function.Injective (a * ·) := fun _ _ h => le_antisymm (ha h.le) (ha h.ge)

