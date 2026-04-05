FAIL
import Mathlib

variable (R : Type u)

variable [Ring R]

theorem free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (ModuleCat.free R).obj X ⟶ M}
    (h : ∀ (x : X), f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) :
    f = g := by
  ext x
  let p : (ModuleCat.free R).obj X := ModuleCat.of R (X →₀ R)
  change f x = g x
  refine Finsupp.induction_linear x ?hzero ?hsingle ?hadd
  · simp
  · intro a x
    simpa [ModuleCat.freeMk, Finsupp.single_eq_same]
      using congrArg (fun y => a • y) (h x)
  · intro a b ha hb
    simp [map_add, ha, hb]
