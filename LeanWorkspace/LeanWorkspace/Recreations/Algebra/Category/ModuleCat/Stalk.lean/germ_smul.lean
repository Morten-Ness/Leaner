import Mathlib

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)

variable (x : X)

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem germ_smul (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m := letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ RingCat).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ _)
    ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _) (Limits.isColimitOfPreserves (forget₂ _ _)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))) (Limits.colimit.isColimit _)
      ⟨_, _⟩ _ _

