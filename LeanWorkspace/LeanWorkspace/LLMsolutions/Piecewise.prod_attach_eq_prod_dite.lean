FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s → M) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [ha, hs, Finset.prod_dite, Finset.mem_insert, dite_eq_ite]
