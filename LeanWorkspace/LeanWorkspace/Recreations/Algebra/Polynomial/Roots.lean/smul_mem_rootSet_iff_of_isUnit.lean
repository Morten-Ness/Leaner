import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem smul_mem_rootSet_iff_of_isUnit [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {g : G} (hg : IsUnit g) {x : R} : g • x ∈ f.rootSet R ↔ x ∈ f.rootSet R := by
  refine ⟨?_, Polynomial.smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx ↦ inv_smul_smul g x ▸ Polynomial.smul_mem_rootSet _ hx

