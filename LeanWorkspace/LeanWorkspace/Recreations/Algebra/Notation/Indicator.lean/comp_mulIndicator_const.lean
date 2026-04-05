import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c := (Set.mulIndicator_comp_of_one hf).symm

