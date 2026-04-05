import Mathlib

variable {M N α β : Type*}

theorem AddMonoidHom.toMultiplicative_id [AddZeroClass α] : (id α).toMultiplicative = .id _ := rfl

