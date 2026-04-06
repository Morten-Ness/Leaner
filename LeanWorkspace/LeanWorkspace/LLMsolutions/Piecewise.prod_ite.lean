FAIL
import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  classical
  simp_rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_filter_mul_prod_filter_not (s := s) (f := fun x => if p x then f x else g x)]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine Finset.prod_congr rfl ?_
    intro x hx
    simp
  · refine Finset.prod_congr rfl ?_
    intro x hx
    simp
