FAIL
import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem points_notMem_affineSpan_faceOpposite [Nontrivial k] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) : s.points i ∉ affineSpan k (Set.range (s.faceOpposite i).points) := by
  classical
  intro hmem
  let t : Fin n → P := (s.faceOpposite i).points
  let j : Fin (n + 1) → Finset (Fin (n + 1)) := fun m => {m}
  have hs :
      AffineIndependent k s.points := s.2
  have hsub :
      Set.range t ⊆ Set.range s.points := by
    intro p hp
    rcases hp with ⟨m, rfl⟩
    rcases Fin.exists_fin_succAbove_eq_iff.mpr rfl with ⟨m, rfl⟩
    exact ⟨i.succAbove m, rfl⟩
  have hspan :
      affineSpan k (Set.range t) ≤ affineSpan k (Set.range s.points) :=
    affineSpan_mono hsub
  have hmem' : s.points i ∈ affineSpan k (Set.range s.points) := by
    exact subset_affineSpan k (by exact ⟨i, rfl⟩)
  have hne :
      s.points i ∉ affineSpan k (Set.range t) := by
    simpa [t] using hs.not_mem_affineSpan_image_finset_erase (f := s.points) (i := i)
  exact hne hmem
