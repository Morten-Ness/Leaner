import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {κ : Type*}

theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    DirectSum.lequivCongrLeft R h f k = f (h.symm k) := equivCongrLeft_apply _ _ _

-- We need to try very hard to avoid dependent type "issues".

