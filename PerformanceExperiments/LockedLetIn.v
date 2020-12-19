Require Import PerformanceExperiments.LetIn.
Require Import PerformanceExperiments.Lock.

Reserved Notation "'nllet' x := v 'in' f"
         (at level 200, f at level 200,
          format "'nllet'  x  :=  v  'in' '//' f").
Definition LockedLet_In_nat : nat -> (nat -> nat) -> nat
  := lock (@Let_In_nd nat nat).
Notation "'nllet' x := v 'in' f"
  := (LockedLet_In_nat v (fun x => f)).
Definition lock_Let_In_nat : @Let_In_nd nat nat = LockedLet_In_nat
  := eq_sym (unlock _).
