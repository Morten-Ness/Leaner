import Mathlib

variable {R S : Type*}

theorem toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) := fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

