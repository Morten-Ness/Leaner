import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem smul_mem_rootSet [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    (g : G) {x : R} (hx : x ∈ f.rootSet R) : g • x ∈ f.rootSet R := by
  simp [Polynomial.mem_rootSet', aeval_smul, Polynomial.aeval_eq_zero_of_mem_rootSet hx, (Polynomial.mem_rootSet'.mp hx).1]

