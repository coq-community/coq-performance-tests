(** * Reification by parametricity *)
Require Import Reify.ReifyCommon.
From Coq Require Import NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.ParametricityCommon.
Require Import Reify.BenchmarkExtraUtil.
Global Open Scope N_scope.

Inductive reif_order := reif_beta | beta_reif.
Record kind := { is_flat : bool ; order : reif_order }.

Definition args_of_size (k : kind) (s : size) : list N
  := match k.(is_flat), k.(order), s with
     | _, _, Sanity => List.firstn 4 sequence
     | _, reif_beta, SuperFast => args_of_max_n 1000
     | _, reif_beta, _         => args_of_max_n 30000
     | _, beta_reif, SuperFast => args_of_max_n 500
     | _, beta_reif, Fast      => args_of_max_n 5000
     | _, beta_reif, _         => args_of_max_n 30000
     end.

Ltac mkgoal kind := let is_flat := (eval cbv in kind.(is_flat)) in BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal kind sz :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in kind.(is_flat)) in
  let order := (eval cbv in kind.(order)) in
  let do_cbv := lazymatch order with
                | reif_beta => BenchmarkExtraUtil.do_cbv_delta
                | beta_reif => BenchmarkExtraUtil.do_cbv
                end in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := ParametricityCommon.do_Reify_rhs do_trans in
  let post_reify := ParametricityCommon.post_Reify_rhs do_trans in
  lazymatch kind with
  | {| is_flat := true ; order := reif_beta |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Parametricity; beta with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Parametricity; beta with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Parametricity; beta with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Parametricity; beta with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Parametricity; beta with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Parametricity; beta with big_flat-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Parametricity; beta with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Parametricity; beta with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Parametricity; beta with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for Parametricity; beta with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for Parametricity; beta with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for Parametricity; beta with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; order := reif_beta |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Parametricity; beta with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Parametricity; beta with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Parametricity; beta with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Parametricity; beta with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Parametricity; beta with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Parametricity; beta with big-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Parametricity; beta with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Parametricity; beta with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Parametricity; beta with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for Parametricity; beta with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for Parametricity; beta with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for Parametricity; beta with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; order := beta_reif |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for beta; Parametricity with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for beta; Parametricity with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for beta; Parametricity with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for beta; Parametricity with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for beta; Parametricity with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for beta; Parametricity with big_flat-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for beta; Parametricity with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for beta; Parametricity with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for beta; Parametricity with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for beta; Parametricity with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for beta; Parametricity with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for beta; Parametricity with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; order := beta_reif |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for beta; Parametricity with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for beta; Parametricity with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for beta; Parametricity with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for beta; Parametricity with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for beta; Parametricity with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for beta; Parametricity with big-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for beta; Parametricity with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for beta; Parametricity with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for beta; Parametricity with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for beta; Parametricity with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for beta; Parametricity with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for beta; Parametricity with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ?kind => fail 0 "Unrecognized kind:" kind
  end.

Ltac do_verify kind :=
  let is_flat := (eval cbv in kind.(is_flat)) in
  BenchmarkExtraUtil.do_verify is_flat.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

for i, (is_flat, order) in enumerate([(is_flat, order) for is_flat in ('true', 'false') for order in ('reif_beta', 'beta_reif')]):
    kind = r'{| is_flat := %s ; order := %s |}' % (is_flat, order)
    print(f'Ltac mkgoal{i} := mkgoal constr:({kind}).\nLtac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac verify{i} := do_verify constr:({kind}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size {kind}) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:({| is_flat := true ; order := reif_beta |}).
Ltac time_solve_goal0 := time_solve_goal constr:({| is_flat := true ; order := reif_beta |}).
Ltac verify0 := do_verify constr:({| is_flat := true ; order := reif_beta |}).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; order := reif_beta |}) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:({| is_flat := true ; order := beta_reif |}).
Ltac time_solve_goal1 := time_solve_goal constr:({| is_flat := true ; order := beta_reif |}).
Ltac verify1 := do_verify constr:({| is_flat := true ; order := beta_reif |}).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; order := beta_reif |}) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Ltac mkgoal2 := mkgoal constr:({| is_flat := false ; order := reif_beta |}).
Ltac time_solve_goal2 := time_solve_goal constr:({| is_flat := false ; order := reif_beta |}).
Ltac verify2 := do_verify constr:({| is_flat := false ; order := reif_beta |}).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; order := reif_beta |}) describe_goal mkgoal2 redgoal ltac:(time_solve_goal2 sz) verify2 sz.

Ltac mkgoal3 := mkgoal constr:({| is_flat := false ; order := beta_reif |}).
Ltac time_solve_goal3 := time_solve_goal constr:({| is_flat := false ; order := beta_reif |}).
Ltac verify3 := do_verify constr:({| is_flat := false ; order := beta_reif |}).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; order := beta_reif |}) describe_goal mkgoal3 redgoal ltac:(time_solve_goal3 sz) verify3 sz.

Global Open Scope N_scope.
(*
Goal True.
  run2 SuperFast.
*)
