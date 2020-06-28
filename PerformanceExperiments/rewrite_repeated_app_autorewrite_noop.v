Require Import PerformanceExperiments.Harness.
Require Export PerformanceExperiments.rewrite_repeated_app_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => List.map (fun x => x * 50) (seq 1 8)
     | Fast => (List.map (fun x => x * 4) (seq 1 250))
                 ++ (List.map (fun x => x * 100) (seq 1 50))
                 ++ (List.map (fun x => x * 500) (seq 1 20))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac do_autorewrite := autorewrite with rew_fg.
Ltac do_rewrite_bang := try rewrite !fg.
Ltac do_rewrite_once := try rewrite fg.
Ltac do_rewrite_ques := try rewrite ?fg.
Require Import Coq.ssr.ssreflect.
Ltac do_ssr_rewrite_bang := try rewrite !fg.
Ltac do_ssr_rewrite_once := try rewrite fg.
Ltac do_ssr_rewrite_ques := try rewrite ?fg.

Ltac time_solve_goal0 n :=
  time "autorewrite-noop-regression-quadratic" do_autorewrite;
  time "try-rewrite!-noop-regression-quadratic" do_rewrite_bang;
  time "try-rewrite-noop-regression-quadratic" do_rewrite_once;
  time "try-rewrite?-noop-regression-quadratic" do_rewrite_ques;
  time "try-ssr-rewrite!-noop-regression-linear" do_ssr_rewrite_bang;
  time "try-ssr-rewrite-noop-regression-linear" do_ssr_rewrite_once;
  time "try-ssr-rewrite?-noop-regression-linear" do_ssr_rewrite_ques;
  reflexivity.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal_noop redgoal time_solve_goal0 sz.

(*
Goal True.
  Time run0 Fast.
 *)
