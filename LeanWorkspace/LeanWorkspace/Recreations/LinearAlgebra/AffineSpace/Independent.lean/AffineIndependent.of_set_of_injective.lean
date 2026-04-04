import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.of_set_of_injective {p : ι → P}
    (ha : AffineIndependent k (fun x => x : Set.range p → P)) (hi : Function.Injective p) :
    AffineIndependent k p := ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

