import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

omit [DecidableRel c.Rel] in
theorem descSigma_ext_iff {φ : F ⟶ G} {K : HomologicalComplex C c}
    (x y : Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) :
    x = y ↔ x.1 = y.1 ∧ (∀ (i j : ι) (_ : c.Rel j i), x.2.hom i j = y.2.hom i j) := by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

