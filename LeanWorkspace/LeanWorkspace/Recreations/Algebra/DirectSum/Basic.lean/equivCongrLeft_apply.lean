import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable {κ : Type*}

theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    DirectSum.equivCongrLeft h f k = f (h.symm k) := by
  exact DFinsupp.comapDomain'_apply _ h.right_inv _ _

