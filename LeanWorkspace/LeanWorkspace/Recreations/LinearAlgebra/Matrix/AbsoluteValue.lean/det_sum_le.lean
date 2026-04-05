import Mathlib

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_sum_le {ι : Type*} (s : Finset ι) {A : ι → Matrix n n R} {abv : AbsoluteValue R S}
    {x : S} (hx : ∀ k i j, abv (A k i j) ≤ x) :
    abv (det (∑ k ∈ s, A k)) ≤ (Fintype.card n)! • (#s • x) ^ Fintype.card n := Matrix.det_le fun i j =>
    calc
      abv ((∑ k ∈ s, A k) i j) = abv (∑ k ∈ s, A k i j) := by simp only [sum_apply]
      _ ≤ ∑ k ∈ s, abv (A k i j) := abv.sum_le _ _
      _ ≤ ∑ _k ∈ s, x := by gcongr; apply hx
      _ = #s • x := sum_const _

