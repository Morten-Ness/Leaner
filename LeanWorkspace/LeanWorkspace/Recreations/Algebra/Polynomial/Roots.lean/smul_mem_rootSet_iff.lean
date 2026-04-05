import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem smul_mem_rootSet_iff [CommRing S] [Algebra S R] {G : Type*}
    [Group G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} {x : R} : g • x ∈ f.rootSet R ↔ x ∈ f.rootSet R := Polynomial.smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)

