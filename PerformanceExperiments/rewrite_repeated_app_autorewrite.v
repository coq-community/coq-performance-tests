Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.HarnessTimeAbstract.
Require Export PerformanceExperiments.rewrite_repeated_app_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 8)
     | Fast => seq 1 100 ++ List.map (fun x => x * 10) (seq 1 40)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  time_abstract_gen
    (fun tac => time "abstract+autorewrite-regression-quadratic" (tac ()))
    restart_timer
    (finish_timing ( "Tactic call close-abstract+autorewrite-regression-quadratic" ))
    (time "autorewrite-regression-quadratic" autorewrite with rew_fg;
     time "autorewrite-noop-regression-linear" autorewrite with rew_fg;
     reflexivity).
Ltac time_solve_goal1 n :=
  time_abstract_gen
    (fun tac => time "abstract+rewrite!-regression-quadratic" (tac ()))
    restart_timer
    (finish_timing ( "Tactic call close-abstract+rewrite!-regression-quadratic" ))
    (time "rewrite!-regression-quadratic" rewrite !fg;
     time "rewrite?-noop-regression-linear" rewrite ?fg;
     reflexivity).

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Ltac run1 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal1 sz.

(*
Goal True.
  run0 Fast.
 *)
