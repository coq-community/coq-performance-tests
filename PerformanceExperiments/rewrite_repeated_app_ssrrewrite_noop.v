From Coq Require Export ZArith.
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

From Coq Require Import ssreflect.
Ltac do_ssr_rewrite_bang := try rewrite !f'g'.
Ltac do_ssr_rewrite_once := try rewrite f'g'.
Ltac do_ssr_rewrite_ques := try rewrite ?f'g'.
Ltac do_ssr_rewrite_bang_evar := try rewrite !(f'g' _).
Ltac do_ssr_rewrite_once_evar := try rewrite (f'g' _).
Ltac do_ssr_rewrite_ques_evar := try rewrite ?(f'g' _).

Ltac time_solve_goal0 n :=
  time "try-ssr-rewrite!-cold-noop-regression-linear" do_ssr_rewrite_bang;
  time "try-ssr-rewrite!-noop-regression-linear" do_ssr_rewrite_bang;
  time "try-ssr-rewrite-noop-regression-linear" do_ssr_rewrite_once;
  time "try-ssr-rewrite?-noop-regression-linear" do_ssr_rewrite_ques;
  time "try-ssr-rewrite!-evar-noop-regression-linear" do_ssr_rewrite_bang_evar;
  time "try-ssr-rewrite-evar-noop-regression-linear" do_ssr_rewrite_once_evar;
  time "try-ssr-rewrite?-evar-noop-regression-linear" do_ssr_rewrite_ques_evar;
  reflexivity.

Ltac run0 sz := Harness.runtests args_of_size describe_goal_noop_exp mkgoal_noop_exp redgoal time_solve_goal0 sz.
Global Open Scope Z_scope.

(*
Goal True.
  Time run0 Fast.
 *)
