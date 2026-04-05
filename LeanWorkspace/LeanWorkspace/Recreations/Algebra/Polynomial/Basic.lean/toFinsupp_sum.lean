import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i : R[X]).toFinsupp = ∑ i ∈ s, (f i).toFinsupp := map_sum (Polynomial.toFinsuppIso R) f s

