import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem isEmbedding_hom :
    IsEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) := ⟨.induced _, fun _ _ e ↦ by ext; rw [e]⟩

