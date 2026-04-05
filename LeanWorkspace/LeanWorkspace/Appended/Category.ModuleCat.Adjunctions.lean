import Mathlib

section

variable (R : Type u)

variable [Ring R]

theorem freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    ModuleCat.freeDesc f (ModuleCat.freeMk x) = f x := by
  dsimp [ModuleCat.freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

end

section

variable (R : Type u)

variable [Ring R]

theorem free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (ModuleCat.free R).obj X ⟶ M}
    (h : ∀ (x : X), f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) :
    f = g := ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

end

section

variable (R : Type u)

variable [Ring R]

theorem free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (ModuleCat.free R).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (f x) := by
  apply Finsupp.mapDomain_single

end

section

variable (R : Type u)

variable [CommRing R]

theorem μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (ModuleCat.FreeMonoidal.μIso R X Y).hom (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) = ModuleCat.freeMk ⟨x, y⟩ := by
  dsimp [ModuleCat.FreeMonoidal.μIso, ModuleCat.freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

end
