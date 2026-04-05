import Mathlib

variable {M : Type*}

theorem mk_surjective [Monoid M] : Function.Surjective (@Associates.mk M _) := Associates.forall_associated.2 fun a => ⟨a, Associated.rfl⟩

