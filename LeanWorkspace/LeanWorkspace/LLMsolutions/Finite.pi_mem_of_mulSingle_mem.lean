FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {η : Type*} {f : η → Type*} [∀ i, Group (f i)]

theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  classical
  letI : Fintype η := Fintype.ofFinite η
  classical
  induction Fintype.elems η using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      have hmul : Pi.mulSingle i (x i) * ∏ j ∈ s, Pi.mulSingle j (x j) ∈ H := by
        exact H.mul_mem (h i) hs
      have hprod :
          (Pi.mulSingle i (x i) * ∏ j ∈ s, Pi.mulSingle j (x j)) = x := by
        ext j
        by_cases hji : j = i
        · subst hji
          simp [hi]
        · simp [Finset.prod_mul_distrib, hji, hi]
      simpa [Finset.prod_insert, hi] using hmul
