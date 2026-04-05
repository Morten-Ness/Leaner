import Mathlib

variable {ι : Type*}

variable {R S : Type*} [SetLike S R]

theorem SetLike.isHomogeneousElem_coe {A : ι → S} {i} (x : A i) :
    SetLike.IsHomogeneousElem A (x : R) := ⟨i, x.prop⟩

