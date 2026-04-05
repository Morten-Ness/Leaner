import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem List.dProdIndex_nil (fι : α → ι) : ([] : List α).dProdIndex fι = 0 := rfl

