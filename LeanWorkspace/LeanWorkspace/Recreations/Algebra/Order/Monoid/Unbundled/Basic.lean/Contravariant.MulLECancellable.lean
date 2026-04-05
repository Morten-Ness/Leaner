import Mathlib

variable {α β : Type*}

theorem Contravariant.MulLECancellable [Mul α] [LE α] [MulLeftReflectLE α]
    {a : α} :
    MulLECancellable a := fun _ _ => le_of_mul_le_mul_left'

