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

theorem coplanar_singleton (p : P) : Coplanar k ({p} : Set P) := (collinear_singleton k p).coplanar

