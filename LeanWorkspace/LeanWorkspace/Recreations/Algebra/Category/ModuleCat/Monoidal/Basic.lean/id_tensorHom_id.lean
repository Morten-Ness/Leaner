import Mathlib

variable {R : Type u} [CommSemiring R]

theorem id_tensorHom_id (M N : SemimoduleCat R) :
    SemimoduleCat.MonoidalCategory.tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

