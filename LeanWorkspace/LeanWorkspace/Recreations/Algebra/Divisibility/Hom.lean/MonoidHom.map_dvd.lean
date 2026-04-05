import Mathlib

variable {M N : Type*}

theorem MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M →* N) {a b} : a ∣ b → f a ∣ f b := map_dvd _root_ f

