import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_sum {ι : Type*} (s : Finset ι) (f : ι → R[ℕ]) :
    (⟨∑ i ∈ s, f i⟩ : R[X]) = ∑ i ∈ s, ⟨f i⟩ := map_sum (Polynomial.toFinsuppIso R).symm f s

