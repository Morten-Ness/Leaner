import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_le_mulIndicator_apply_of_subset (h : s ⊆ t) (hf : 1 ≤ f a) :
    mulIndicator s f a ≤ mulIndicator t f a := Set.mulIndicator_apply_le'
    (fun ha ↦ Set.le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    Set.one_le_mulIndicator_apply fun _ ↦ hf

