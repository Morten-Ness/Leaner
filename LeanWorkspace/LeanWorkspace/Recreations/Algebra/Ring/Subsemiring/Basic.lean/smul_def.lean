import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {R' α β : Type*}

variable {S' : Type*} [SetLike S' R'] (s : S)

variable [NonAssocSemiring R']

theorem smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m := rfl

