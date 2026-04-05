import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem sum_mem (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι → R}
    (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s := sum_mem h

