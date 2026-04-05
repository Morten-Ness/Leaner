import Mathlib

variable {M : Type*}

theorem of_val (a : MulArchimedeanOrder M) : MulArchimedeanOrder.of (MulArchimedeanOrder.val a) = a := rfl

