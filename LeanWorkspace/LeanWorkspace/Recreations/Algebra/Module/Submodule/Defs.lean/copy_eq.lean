import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S := SetLike.coe_injective hs

