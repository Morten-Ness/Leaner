import Mathlib

variable {R : Type*}

theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)

