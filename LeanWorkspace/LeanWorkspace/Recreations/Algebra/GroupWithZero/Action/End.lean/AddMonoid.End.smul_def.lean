import Mathlib

variable {M N A α β : Type*}

theorem AddMonoid.End.smul_def [AddMonoid α] (f : AddMonoid.End α) (a : α) : f • a = f a := rfl

