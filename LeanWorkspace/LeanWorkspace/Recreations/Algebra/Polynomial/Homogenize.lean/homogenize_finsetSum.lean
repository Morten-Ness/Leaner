import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_finsetSum {ι : Type*} (s : Finset ι) (p : ι → R[X]) (n : ℕ) :
    Polynomial.homogenize (∑ i ∈ s, p i) n = ∑ i ∈ s, Polynomial.homogenize (p i) n := _root_.map_sum (Polynomial.homogenizeLM n) p s

