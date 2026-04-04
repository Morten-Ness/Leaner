import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

theorem toMatrix_apply {ι' : Type*} (q : ι' → P) (i : ι') (j : ι) :
    b.toMatrix q i j = b.coord j (q i) := rfl

