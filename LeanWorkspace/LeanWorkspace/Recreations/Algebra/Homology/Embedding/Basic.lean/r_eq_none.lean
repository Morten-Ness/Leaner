import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem r_eq_none (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    e.r i' = none := dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

