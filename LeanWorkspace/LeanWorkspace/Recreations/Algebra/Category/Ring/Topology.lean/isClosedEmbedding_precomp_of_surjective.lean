import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem isClosedEmbedding_precomp_of_surjective
    [T1Space R] (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine ⟨CommRingCat.HomTopology.isEmbedding_precomp_of_surjective f hf, ?_⟩
  have : IsClosed (⋂ i : RingHom.ker f.hom, { f : A ⟶ R | f i = 0 }) :=
    isClosed_iInter fun x ↦ (isClosed_singleton (x := 0)).preimage (continuous_apply (R := R) x.1)
  convert this
  ext x
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall, RingHom.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩ a ha; simp [ha]
  · exact fun H ↦ ⟨CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨x.hom, H⟩),
      by ext; simp [RingHom.liftOfRightInverse_comp_apply]⟩

