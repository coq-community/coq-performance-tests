Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.rewrite_under_binders_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 4)
     | Fast => List.map (fun x => x * 10) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  (time "noop-repeat-setoid_rewrite-regression-cubic" repeat setoid_rewrite <- plus_n_O);
  (time "noop-repeat-rewrite_strat-topdown-regression-cubic" repeat rewrite_strat topdown <- plus_n_O);
  (time "noop-repeat-rewrite_strat-bottomup-regression-cubic" repeat rewrite_strat bottomup <- plus_n_O).

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal_noop redgoal time_solve_goal0 sz.

(*
Goal True.
  run0 Fast.
 *)
