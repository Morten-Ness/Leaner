import Mathlib

variable (ι : Type v) (β : ι → Type w)

theorem coeFnAddMonoidHom_apply [∀ i, AddCommMonoid (β i)] (v : ⨁ i, β i) :
    DirectSum.coeFnAddMonoidHom β v = v := rfl

