(** * Reification by Ltac2 *)
Require Import Reify.ReifyCommon.
From Coq Require Import NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.Ltac2Reify.
Require Import Reify.BenchmarkExtraUtil.
Global Open Scope N_scope.

Inductive checked_kind := checked | unchecked.
Inductive rkind := normal | low_level (checked : checked_kind).
Record kind := { is_flat : bool ; reif_kind : rkind }.

Definition args_of_size (k : kind) (s : size) : list N
  := match k.(is_flat), k.(reif_kind), s with
     | _    , _, Sanity => List.firstn 4 sequence
     | _    , low_level _, SuperFast => args_of_max_n  1000
     | _    , low_level _, _         => args_of_max_n 30000
     | true , normal     , SuperFast => args_of_max_n   500
     | true , normal     , Fast      => args_of_max_n  6000
     | true , normal     , _         => args_of_max_n 30000
     | false, normal     , SuperFast => args_of_max_n    50
     | false, normal     , Fast      => args_of_max_n   300
     | false, normal     , Medium    => args_of_max_n  1450
     | false, normal     , _         => args_of_max_n 30000
     end.

Ltac mkgoal kind := let is_flat := (eval cbv in kind.(is_flat)) in BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.

Ltac time_solve_goal kind sz :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in kind.(is_flat)) in
  let reif_kind := (eval cbv in kind.(reif_kind)) in
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := lazymatch reif_kind with
                  | normal => Ltac2.do_Reify_rhs do_trans
                  | low_level checked => Ltac2LowLevel.do_Reify_rhs do_trans
                  | low_level unchecked => Ltac2LowLevel.do_unsafe_Reify_rhs do_trans
                  end in
  let post_reify := lazymatch reif_kind with
                    | normal => Ltac2.post_Reify_rhs do_trans
                    | low_level checked => Ltac2LowLevel.post_Reify_rhs do_trans
                    | low_level unchecked => Ltac2LowLevel.post_unsafe_Reify_rhs do_trans
                    end in
  lazymatch kind with
  | {| is_flat := true ; reif_kind := normal |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2 with big_flat") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2 with big_flat") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2 with big_flat") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2 with big_flat") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2 with big_flat") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2 with big_flat") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2 with big_flat" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2 with big_flat" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2 with big_flat" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2 with big_flat" pre_reify  x in
       let do_reify   x := time "reif for Ltac2 with big_flat" do_reify   x in
       let post_reify x := time "post for Ltac2 with big_flat" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; reif_kind := low_level unchecked |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2LowLevel with big_flat") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2LowLevel with big_flat") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2LowLevel with big_flat") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2LowLevel with big_flat") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2LowLevel with big_flat") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2LowLevel with big_flat") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2LowLevel with big_flat" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2LowLevel with big_flat" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2LowLevel with big_flat" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2LowLevel with big_flat" pre_reify  x in
       let do_reify   x := time "reif for Ltac2LowLevel with big_flat" do_reify   x in
       let post_reify x := time "post for Ltac2LowLevel with big_flat" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; reif_kind := low_level checked |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2LowLevelChecked with big_flat") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2LowLevelChecked with big_flat") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2LowLevelChecked with big_flat") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2LowLevelChecked with big_flat") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2LowLevelChecked with big_flat") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2LowLevelChecked with big_flat") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2LowLevelChecked with big_flat" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2LowLevelChecked with big_flat" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2LowLevelChecked with big_flat" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2LowLevelChecked with big_flat" pre_reify  x in
       let do_reify   x := time "reif for Ltac2LowLevelChecked with big_flat" do_reify   x in
       let post_reify x := time "post for Ltac2LowLevelChecked with big_flat" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; reif_kind := normal |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2 with big") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2 with big") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2 with big") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2 with big") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2 with big") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2 with big") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2 with big" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2 with big" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2 with big" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2 with big" pre_reify  x in
       let do_reify   x := time "reif for Ltac2 with big" do_reify   x in
       let post_reify x := time "post for Ltac2 with big" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; reif_kind := low_level unchecked |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2LowLevel with big") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2LowLevel with big") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2LowLevel with big") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2LowLevel with big") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2LowLevel with big") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2LowLevel with big") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2LowLevel with big" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2LowLevel with big" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2LowLevel with big" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2LowLevel with big" pre_reify  x in
       let do_reify   x := time "reif for Ltac2LowLevel with big" do_reify   x in
       let post_reify x := time "post for Ltac2LowLevel with big" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; reif_kind := low_level checked |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for Ltac2LowLevelChecked with big") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for Ltac2LowLevelChecked with big") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for Ltac2LowLevelChecked with big") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for Ltac2LowLevelChecked with big") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for Ltac2LowLevelChecked with big") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for Ltac2LowLevelChecked with big") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for Ltac2LowLevelChecked with big" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for Ltac2LowLevelChecked with big" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for Ltac2LowLevelChecked with big" do_cbv     x in
       let pre_reify  x := time  "pre for Ltac2LowLevelChecked with big" pre_reify  x in
       let do_reify   x := time "reif for Ltac2LowLevelChecked with big" do_reify   x in
       let post_reify x := time "post for Ltac2LowLevelChecked with big" post_reify x in
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

checked_kind = ('checked', 'unchecked')
rkind = ['normal'] + ['low_level ' + k for k in checked_kind]
for i, (is_flat, k) in enumerate([(is_flat, k) for is_flat in ('true', 'false') for k in rkind]):
    kind = r'{| is_flat := %s ; reif_kind := %s |}' % (is_flat, k)
    print(f'Ltac mkgoal{i} := mkgoal constr:({kind}).\nLtac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac verify{i} := do_verify constr:({kind}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size {kind}) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:({| is_flat := true ; reif_kind := normal |}).
Ltac time_solve_goal0 := time_solve_goal constr:({| is_flat := true ; reif_kind := normal |}).
Ltac verify0 := do_verify constr:({| is_flat := true ; reif_kind := normal |}).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; reif_kind := normal |}) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:({| is_flat := true ; reif_kind := low_level checked |}).
Ltac time_solve_goal1 := time_solve_goal constr:({| is_flat := true ; reif_kind := low_level checked |}).
Ltac verify1 := do_verify constr:({| is_flat := true ; reif_kind := low_level checked |}).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; reif_kind := low_level checked |}) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Ltac mkgoal2 := mkgoal constr:({| is_flat := true ; reif_kind := low_level unchecked |}).
Ltac time_solve_goal2 := time_solve_goal constr:({| is_flat := true ; reif_kind := low_level unchecked |}).
Ltac verify2 := do_verify constr:({| is_flat := true ; reif_kind := low_level unchecked |}).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; reif_kind := low_level unchecked |}) describe_goal mkgoal2 redgoal ltac:(time_solve_goal2 sz) verify2 sz.

Ltac mkgoal3 := mkgoal constr:({| is_flat := false ; reif_kind := normal |}).
Ltac time_solve_goal3 := time_solve_goal constr:({| is_flat := false ; reif_kind := normal |}).
Ltac verify3 := do_verify constr:({| is_flat := false ; reif_kind := normal |}).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; reif_kind := normal |}) describe_goal mkgoal3 redgoal ltac:(time_solve_goal3 sz) verify3 sz.

Ltac mkgoal4 := mkgoal constr:({| is_flat := false ; reif_kind := low_level checked |}).
Ltac time_solve_goal4 := time_solve_goal constr:({| is_flat := false ; reif_kind := low_level checked |}).
Ltac verify4 := do_verify constr:({| is_flat := false ; reif_kind := low_level checked |}).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; reif_kind := low_level checked |}) describe_goal mkgoal4 redgoal ltac:(time_solve_goal4 sz) verify4 sz.

Ltac mkgoal5 := mkgoal constr:({| is_flat := false ; reif_kind := low_level unchecked |}).
Ltac time_solve_goal5 := time_solve_goal constr:({| is_flat := false ; reif_kind := low_level unchecked |}).
Ltac verify5 := do_verify constr:({| is_flat := false ; reif_kind := low_level unchecked |}).
Ltac run5 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; reif_kind := low_level unchecked |}) describe_goal mkgoal5 redgoal ltac:(time_solve_goal5 sz) verify5 sz.

Global Open Scope N_scope.
(*
Goal True.
  run5 Sanity.
*)
