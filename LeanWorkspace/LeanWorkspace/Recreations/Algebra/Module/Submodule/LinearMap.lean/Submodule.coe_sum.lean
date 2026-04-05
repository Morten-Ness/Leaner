import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i ∈ s, x i) = ∑ i ∈ s, (x i : M) := map_sum p.subtype _ _

