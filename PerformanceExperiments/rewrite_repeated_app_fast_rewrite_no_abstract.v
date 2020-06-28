Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.rewrite_repeated_app_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 8)
     | Fast => (seq 1 100)
                 ++ List.map (fun x => x * 10) (seq 1 100)
                 ++ List.map (fun x => x * 100) (seq 1 20)
                 ++ List.map (fun x => x * 1000) (seq 1 5)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac time_solve_goal0 n :=
  time "fast_rewrite-regression-cubic" fast_rewrite.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True.
  Time run0 Fast.
 *)
