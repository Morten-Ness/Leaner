import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem map_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note «slow-failing instance priority» /--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
* a class `C` has instances `instT : C T` and `instT' : C T'`;
* types `T` and `T'` are both reducible specializations of another type `S`;
* the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
  instead they have to be found by instance search.

If those conditions hold, the instance `instT` should be assigned lower priority.

Note that there is no issue unless `T` and `T'` are reducibly equal to `S`, Otherwise the instance
discrimination tree can distinguish them, and the note does not apply.

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/

