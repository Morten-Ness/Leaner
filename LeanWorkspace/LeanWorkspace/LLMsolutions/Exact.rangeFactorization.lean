FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem rangeFactorization [One P] (h : Function.MulExact f g) (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    Function.Surjective (show M → Set.range g from fun x => ⟨g (f x), ⟨f x, rfl⟩⟩) := by
  dsimp
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨n, rfl⟩
  have hgn : g n = 1 := by
    rw [Function.MulExact] at h
    exact (h n).mpr ⟨n, rfl⟩
  have hn : n ∈ Set.range f := by
    rw [Function.MulExact] at h
    exact (h n).mp hgn
  rcases hn with ⟨x, rfl⟩
  exact ⟨x, rfl⟩
