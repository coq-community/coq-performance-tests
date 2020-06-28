Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.HarnessTimeAbstract.
Require Export PerformanceExperiments.rewrite_under_binders_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 10) (seq 1 4)
     | Fast => seq 0 25 ++ List.map (fun x => x * 5) (seq 1 10)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  time_abstract_gen
    (fun tac => time "abstract+repeat-rewrite_strat-topdown-regression-cubic" (tac ()))
    restart_timer
    (finish_timing ( "Tactic call close-abstract+repeat-rewrite_strat-topdown-regression-quadratic" ))
    ((time "repeat-rewrite_strat-topdown-regression-cubic" repeat rewrite_strat topdown <- plus_n_O);
     (time "noop-repeat-rewrite_strat-topdown-regression-cubic" repeat rewrite_strat topdown <- plus_n_O)).
Ltac time_solve_goal1 n :=
  time_abstract_gen
    (fun tac => time "abstract+repeat-rewrite_strat-bottomup-regression-cubic" (tac ()))
    restart_timer
    (finish_timing ( "Tactic call close-abstract+repeat-rewrite_strat-bottomup-regression-quadratic" ))
    ((time "repeat-rewrite_strat-bottomup-regression-cubic" repeat rewrite_strat bottomup <- plus_n_O);
     (time "noop-repeat-rewrite_strat-bottomup-regression-cubic" repeat rewrite_strat bottomup <- plus_n_O)).

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Ltac run1 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal1 sz.

(*
Goal True.
  run0 Fast.
 *)
