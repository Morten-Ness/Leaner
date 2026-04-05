import Mathlib

variable {M : Type*}

theorem of_symm_eq : (MulArchimedeanOrder.of (M := M)).symm = MulArchimedeanOrder.val := rfl

