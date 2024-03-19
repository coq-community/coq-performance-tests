(** Testing the performance of [zify] and [Z.to_euclidean_division_equations].
For not regressing on COQBUG(https://github.com/coq/coq/issues/18770) *)
From Coq Require Import ZArith List Zify.
Import ListNotations.
Require Import PerformanceExperiments.Harness.

Global Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac mkgoal n := constr:(fold_left (fun T _ => (forall x, 0 <= x < 100 -> T)) (repeat tt (Z.to_nat n)) True).
Ltac redgoal _ := lazy -[Z.le Z.lt]; intros.

Ltac time_solve_goal0 n :=
  time "zify-big-context-regression-quadratic" zify.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 1 3)
     | SuperFast => List.map Z.of_nat (seq 1 45)
     | Fast => List.map (fun x => Z.of_nat x * 50) (seq 1 4)
     | Medium => List.map (fun x => Z.of_nat x * 100) (seq 1 10) ++ [1500; 2000]
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. Time run0 Fast.
*)
