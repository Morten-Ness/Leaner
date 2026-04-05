import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem isEmbedding_precomp_of_surjective
    (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine IsEmbedding.of_comp (CommRingCat.HomTopology.continuous_precomp _) (IsInducing.induced _).continuous ?_
  suffices IsEmbedding ((· ∘ f.hom) : (B → R) → (A → R)) from
    this.comp (.induced (fun f g e ↦ by ext a; exact congr($e a)))
  exact Function.Surjective.isEmbedding_comp _ hf

