import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_one : Submonoid.powers (1 : M) = ⊥ := bot_unique <| Submonoid.powers_le.2 <| one_mem _

