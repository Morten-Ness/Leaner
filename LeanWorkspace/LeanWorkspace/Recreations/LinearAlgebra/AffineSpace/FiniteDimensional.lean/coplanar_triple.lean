import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

variable (k)

theorem coplanar_triple (p₁ p₂ p₃ : P) : Coplanar k ({p₁, p₂, p₃} : Set P) := (collinear_pair k p₂ p₃).coplanar_insert p₁

