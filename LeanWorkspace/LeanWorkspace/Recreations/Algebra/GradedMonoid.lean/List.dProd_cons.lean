import Mathlib

variable {ι : Type*}

variable {α : Type*} {A : ι → Type*} [AddMonoid ι] [GradedMonoid.GMonoid A]

theorem List.dProd_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) :) := rfl

