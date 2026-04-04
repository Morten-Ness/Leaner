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

theorem coplanar_empty : Coplanar k (∅ : Set P) := (collinear_empty k P).coplanar

