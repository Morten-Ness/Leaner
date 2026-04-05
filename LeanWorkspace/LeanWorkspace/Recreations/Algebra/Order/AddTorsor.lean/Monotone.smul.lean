import Mathlib

variable {G P : Type*}

theorem Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [IsOrderedSMul G P] {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x := fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

