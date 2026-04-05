import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (DirectSum.of (fun i => A i) i x) = x := DirectSum.toAddMonoid_of _ _ _

