import Mathlib

variable {R : Type*} [Semiring R]
    {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

theorem coe_congrAddEquiv (u : (i : ι) → N i ≃+ P i) :
    ⇑(DirectSum.congrAddEquiv u).toAddMonoidHom = ⇑(DirectSum.map fun i ↦ (u i).toAddMonoidHom) := rfl

