import Mathlib

section

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem hom_inv_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).inv.hom = (Algebra.TensorProduct.assoc R R R M N K).symm.toAlgHom := rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (AlgCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
        ModuleCat.hom_ext <| TensorProduct.ext_threefold (fun _ _ _ => rfl)
      leftUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl)
      rightUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl) }

end
