import Mathlib

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_le {A : Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
    abv A.det ≤ (Fintype.card n)! • x ^ Fintype.card n := calc
    abv A.det = abv (∑ σ : Perm n, Perm.sign σ • ∏ i, A (σ i) i) := congr_arg abv (det_apply _)
    _ ≤ ∑ σ : Perm n, abv (Perm.sign σ • ∏ i, A (σ i) i) := abv.sum_le _ _
    _ = ∑ σ : Perm n, ∏ i, abv (A (σ i) i) :=
      sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod]
    _ ≤ ∑ _σ : Perm n, ∏ _i : n, x := by gcongr; simp [hx]
    _ = (Fintype.card n)! • x ^ Fintype.card n := by simp [Fintype.card_perm]

