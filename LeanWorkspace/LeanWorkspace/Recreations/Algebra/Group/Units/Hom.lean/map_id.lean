import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_id : Units.map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext; rfl

