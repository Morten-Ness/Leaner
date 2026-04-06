FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {M N : Type*} [CommGroup M] [CommGroup N]

theorem map_range_powMonoidHom (e : M ≃* N) (n : ℕ) :
    (powMonoidHom (α := M) n).range.map e.toMonoidHom = (powMonoidHom (α := N) n).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, by simp [powMonoidHom]⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y ^ n, ?_, ?_⟩
    · exact ⟨e.symm y, rfl⟩
    · simp [powMonoidHom]
