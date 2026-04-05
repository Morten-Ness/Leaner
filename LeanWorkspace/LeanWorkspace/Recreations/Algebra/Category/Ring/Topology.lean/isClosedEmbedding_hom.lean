import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem isClosedEmbedding_hom [IsTopologicalRing R] [T1Space R] :
    IsClosedEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) := by
  let f : CommRingCat.of (MvPolynomial A (⊥_ CommRingCat)) ⟶ A :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (initial.to A).hom id)
  have : Function.Surjective f := Function.LeftInverse.surjective (g := .X) fun x ↦ by simp [f]
  convert ((CommRingCat.HomTopology.mvPolynomialHomeomorph A R (.of _)).trans
    (.uniqueProd (⊥_ CommRingCat ⟶ R) _)).isClosedEmbedding.comp
    (CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective f this) using 2 with g
  ext x
  simp +instances [f]

