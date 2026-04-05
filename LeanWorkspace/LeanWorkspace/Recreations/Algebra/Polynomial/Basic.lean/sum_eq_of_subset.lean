import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) {s : Finset ℕ} (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) := Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

