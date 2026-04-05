import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem coe_powers (x : M) : ↑(Submonoid.powers x) = Set.range fun n : ℕ => x ^ n := rfl

