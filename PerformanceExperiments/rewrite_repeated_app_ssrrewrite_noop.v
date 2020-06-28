Require Export Coq.ZArith.ZArith.
Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.rewrite_repeated_app_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => seq 1 15
     | Fast => seq 1 22
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Require Import Coq.ssr.ssreflect.
Ltac do_ssr_rewrite_bang := try rewrite !f'g'.
Ltac do_ssr_rewrite_once := try rewrite f'g'.
Ltac do_ssr_rewrite_ques := try rewrite ?f'g'.

Ltac time_solve_goal0 n :=
  time "try-ssr-rewrite!-cold-noop-regression-linear" do_ssr_rewrite_bang;
  time "try-ssr-rewrite!-noop-regression-linear" do_ssr_rewrite_bang;
  time "try-ssr-rewrite-noop-regression-linear" do_ssr_rewrite_once;
  time "try-ssr-rewrite?-noop-regression-linear" do_ssr_rewrite_ques;
  reflexivity.

Ltac run0 sz := Harness.runtests args_of_size describe_goal_noop_exp mkgoal_noop_exp redgoal time_solve_goal0 sz.
Global Open Scope Z_scope.

(*
Goal True.
  Time run0 Fast.
 *)
