import Mathlib

open scoped Function

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem Finset.squarefree_prod_of_pairwise_isCoprime {ι : Type*} {s : Finset ι}
    {f : ι → R} (hs : Set.Pairwise s (IsRelPrime on f)) (hs' : ∀ i ∈ s, Squarefree (f i)) :
    Squarefree (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, squarefree_mul_iff]
    rw [Finset.coe_cons, Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi ↦ ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fun h ↦ ha (h ▸ hi)).left
    · exact ih hs.left fun i hi ↦ hs' i <| Finset.mem_cons_of_mem hi

