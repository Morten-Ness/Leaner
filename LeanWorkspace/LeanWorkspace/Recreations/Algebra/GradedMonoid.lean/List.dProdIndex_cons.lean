import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι := rfl

