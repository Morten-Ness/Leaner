import Mathlib

variable {α β : Type*}

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

theorem Equiv.dvd_apply {G : Type*} [LeftCancelSemigroup G] (g a : G) :
    Equiv.dvd g a = g * a := rfl

