import Mathlib

section

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} := Set.ext fun _ => ConjClasses.mem_carrier_iff_mk_eq

end

section

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) := Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

end

section

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ ConjClasses.carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [ConjClasses.forall_isConj]
  intro b
  rw [ConjClasses.carrier, eq_comm, ConjClasses.mk_eq_mk_iff_isConj, ← ConjClasses.quotient_mk_eq_mk, Quotient.lift_mk]
  rfl

end

section

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) := ⟨ConjClasses.mk_injective, ConjClasses.mk_surjective⟩

end

section

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b := Iff.intro Quotient.exact Quot.sound

end

section

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (ConjClasses.mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

end

section

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) := ConjClasses.forall_isConj.2 fun a => ⟨a, rfl⟩

end
