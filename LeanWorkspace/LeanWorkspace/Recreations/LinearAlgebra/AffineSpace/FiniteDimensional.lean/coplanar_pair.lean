import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

variable (k) (P)

theorem coplanar_pair (p₁ p₂ : P) : Coplanar k ({p₁, p₂} : Set P) := (collinear_pair k p₁ p₂).coplanar

