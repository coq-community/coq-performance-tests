Require Import PerformanceExperiments.Harness.
Definition Let_In {A P} (v : A) (f : forall x : A, P x) : P v
:= let x := v in f x.

Fixpoint big (a : nat) (sz : nat) : nat
  := match sz with
     | O => a
     | S sz' => Let_In (a * a) (fun a' => big a' sz')
     end.

Global Set Warnings Append "-abstract-large-number".

Ltac mkgoal n := constr:(exists e, e = big 1 (Z.to_nat n)).
Ltac redgoal _ := lazy -[big]; lazy [big].
Ltac time_solve_goal0 n :=
  lazymatch (eval vm_compute in (6000 <=? n)%Z) with
  | true => optimize_heap
  | false => idtac
  end;
  time "pattern-regression-linear" pattern Nat.mul, S, O, (@Let_In nat (fun _ => nat)).

Global Open Scope Z_scope.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 1 3)
     | SuperFast => List.map Z.of_nat (seq 1 500)
     | Fast => List.map (fun x => Z.of_nat x * 200) (seq 1 100)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. run0 Fast.
*)
