Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.HarnessTimeAbstract.
Require Export PerformanceExperiments.rewrite_under_binders_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 4)
     | Fast => (List.map (fun x => x * 10) (seq 1 25))
                 ++ (List.map (fun x => x * 100) (seq 1 4))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  ((time "repeat-setoid_rewrite-regression-cubic" repeat setoid_rewrite <- plus_n_O);
   (time "noop-repeat-setoid_rewrite-regression-cubic" repeat setoid_rewrite <- plus_n_O)).

Ltac time_solve_goal1 n :=
  time_abstract_gen
    (fun tac => time "abstract+setoid_rewrite-regression-cubic" (tac ()))
    restart_timer
    (finish_timing ( "Tactic call close-abstract+setoid_rewrite-regression-quadratic" ))
    (time "setoid_rewrite-regression-cubic" setoid_rewrite <- plus_n_O).

Ltac time_solve_goal2 n :=
  (time "noop-try-setoid_rewrite-regression-cubic" try setoid_rewrite <- plus_n_O).

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Ltac run1 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal1 sz.
Ltac run2 sz := Harness.runtests args_of_size default_describe_goal mkgoal_noop redgoal time_solve_goal2 sz.

(*
Goal True.
  run0 SuperFast.
 *)
