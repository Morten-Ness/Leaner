FAIL
import Mathlib

open scoped Nat

variable {R S : Type*} [CommRing R] [Nontrivial R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_le {A : Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : ∀ i j, abv (A i j) ≤ x) :
    abv A.det ≤ (Fintype.card n)! • x ^ Fintype.card n := by
  classical
  rw [Matrix.det_apply]
  calc
    abv (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i)
        ≤ ∑ σ : Equiv.Perm n, abv (Equiv.Perm.sign σ • ∏ i, A (σ i) i) := by
          simpa using map_sum_le abv (fun σ : Equiv.Perm n => Equiv.Perm.sign σ • ∏ i, A (σ i) i)
    _ ≤ ∑ σ : Equiv.Perm n, x ^ Fintype.card n := by
          refine Finset.sum_le_sum ?_
          intro σ hσ
          calc
            abv (Equiv.Perm.sign σ • ∏ i, A (σ i) i)
                = abv (Equiv.Perm.sign σ) * abv (∏ i, A (σ i) i) := by
                    simpa [smul_eq_mul] using map_mul abv (Equiv.Perm.sign σ) (∏ i, A (σ i) i)
            _ ≤ 1 * abv (∏ i, A (σ i) i) := by
                  gcongr
                  simpa using abv.map_units_zpow_le_one (Equiv.Perm.sign σ)
            _ = abv (∏ i, A (σ i) i) := by simp
            _ ≤ ∏ i, x := by
                  simpa using map_prod_le abv (fun i => A (σ i) i) (fun i => hx (σ i) i)
            _ = x ^ Fintype.card n := by simp
    _ = (Fintype.card n)! • x ^ Fintype.card n := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp [Fintype.card_perm]
