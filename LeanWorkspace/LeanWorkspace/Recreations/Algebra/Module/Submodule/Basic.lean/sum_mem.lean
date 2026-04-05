import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem sum_mem {t : Finset ι} {f : ι → M} : (∀ c ∈ t, f c ∈ p) → (∑ i ∈ t, f i) ∈ p := sum_mem

