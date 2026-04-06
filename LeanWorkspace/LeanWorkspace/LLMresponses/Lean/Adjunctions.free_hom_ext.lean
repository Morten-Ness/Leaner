FAIL
import Mathlib

variable (R : Type u)

variable [Ring R]

theorem free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (ModuleCat.free R).obj X ⟶ M}
    (h : ∀ (x : X), f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) :
    f = g := by
  ext x
  refine Submodule.span_induction x ?h0 ?hadd ?hsmul ?hmem
  · simp
  · intro a b ha hb
    simp [map_add, ha, hb]
  · intro r a ha
    simp [map_smul, ha]
  · intro y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨r, rfl⟩
    simp [h y]
