FAIL
import Mathlib

theorem val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) := by
  refine ⟨⟨φ a, φ (-a), ?_, ?_⟩, rfl⟩
  · simpa using φ.map_add a (-a)
  · simpa [add_comm] using φ.map_add (-a) a
