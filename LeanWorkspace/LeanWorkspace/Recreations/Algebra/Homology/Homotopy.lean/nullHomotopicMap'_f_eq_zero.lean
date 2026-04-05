import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

theorem nullHomotopicMap'_f_eq_zero {k₀ : ι} (hk₀ : ∀ l : ι, ¬c.Rel k₀ l)
    (hk₀' : ∀ l : ι, ¬c.Rel l k₀) (h : ∀ i j, c.Rel j i → (C.X i ⟶ D.X j)) :
    (Homotopy.nullHomotopicMap' h).f k₀ = 0 := by
  simp only [Homotopy.nullHomotopicMap']
  apply Homotopy.nullHomotopicMap_f_eq_zero hk₀ hk₀'

