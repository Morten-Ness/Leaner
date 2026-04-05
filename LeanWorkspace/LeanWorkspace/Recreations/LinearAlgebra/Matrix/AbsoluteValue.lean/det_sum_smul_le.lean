import Mathlib

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_sum_smul_le {ι : Type*} (s : Finset ι) {c : ι → R} {A : ι → Matrix n n R}
    {abv : AbsoluteValue R S} {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) {y : S}
    (hy : ∀ k, abv (c k) ≤ y) :
    abv (det (∑ k ∈ s, c k • A k)) ≤
      Nat.factorial (Fintype.card n) • (#s • y * x) ^ Fintype.card n := by
  simpa only [smul_mul_assoc] using
    Matrix.det_sum_le s fun k i j =>
      calc
        abv (c k * A k i j) = abv (c k) * abv (A k i j) := abv.map_mul _ _
        _ ≤ y * x := mul_le_mul (hy k) (hx k i j) (abv.nonneg _) ((abv.nonneg _).trans (hy k))

