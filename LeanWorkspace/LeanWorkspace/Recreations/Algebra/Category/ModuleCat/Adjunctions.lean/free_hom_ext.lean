import Mathlib

variable (R : Type u)

variable [Ring R]

theorem free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (ModuleCat.free R).obj X ⟶ M}
    (h : ∀ (x : X), f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) :
    f = g := ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

