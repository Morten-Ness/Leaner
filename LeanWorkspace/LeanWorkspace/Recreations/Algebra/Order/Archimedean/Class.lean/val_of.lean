import Mathlib

variable {M : Type*}

theorem val_of (a : M) : MulArchimedeanOrder.val (MulArchimedeanOrder.of a) = a := rfl

