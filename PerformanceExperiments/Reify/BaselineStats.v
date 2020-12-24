Require Import Reify.Common.
Require Import Reify.BenchmarkUtil.
Require Import Reify.PHOAS.
Require Import Reify.BenchmarkExtraUtil.
Require Import PerformanceExperiments.Harness.

Inductive partial_red_kind := cbv | lazy | simpl | cbn.
Inductive full_red_kind := vm_compute | native_compute.
Inductive red := partial (_ : partial_red_kind) | full (_ : full_red_kind).
Coercion full : full_red_kind >-> red.
Coercion partial : partial_red_kind >-> red.
Inductive red_kind := identity (r : red) | red_Denote (r : partial_red_kind).
Inductive any_kind := rkind (r : red_kind) | refine_let | transitivity.
Coercion rkind : red_kind >-> any_kind.
Record kind := { is_flat : bool ; tactic : any_kind }.

Module Export Exports.
  Global Arguments Let_In : simpl never.
  Global Arguments Nat.mul : simpl never.
  Global Arguments PHOAS.denote / .
  Global Arguments PHOAS.Denote / .
End Exports.

Definition is_native (k : kind) : bool
  := match k.(tactic) with
     | identity native_compute
       => true
     | identity _
     | red_Denote _
     | refine_let
     | transitivity
       => false
     end.

Definition args_of_size (k : kind) (s : size) : list N
  := match is_native k, k.(is_flat), s with
     | _, _, Sanity => List.firstn 4 sequence
     | false, true , SuperFast => args_of_max_n   500
     | false, true , Fast      => args_of_max_n 12500
     | false, true , Medium    => args_of_max_n 30000
     | false, false, SuperFast => args_of_max_n   500
     | false, false, Fast      => args_of_max_n  3000
     | false, false, Medium    => args_of_max_n 10000
     | false, _    , _         => args_of_max_n 30000

     | true , true , SuperFast => args_of_max_n    50
     | true , true , Fast      => args_of_max_n 12500
     | true , true , Medium    => args_of_max_n 30000
     | true , true , _         => args_of_max_n 30000
     | true , false, SuperFast => args_of_max_n   200
     | true , false, Fast      => args_of_max_n   800
     | true , false, Medium    => args_of_max_n  4000
     | true , false, _         => args_of_max_n  5000
     end.

Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal kind :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in kind.(is_flat)) in
  let tactic := (eval cbv in kind.(tactic)) in
  let ref_PHOAS := ref_PHOAS_of is_flat in
  fun n
  => let ref_PHOAS := ref_PHOAS n in
     lazymatch kind with
     | {| is_flat := true ; tactic := refine_let |}
       => time "refine let on PHOAS with big_flat-regression-quadratic"
               (idtac; let p := fresh in refine (let p := ref_PHOAS in _))
     | {| is_flat := true ; tactic := transitivity |}
       => time "transitivity on PHOAS with big_flat-regression-quadratic"
               (idtac;
                let p := fresh in
                assert (p : O = O);
                [ transitivity (Denote ref_PHOAS) | ])
     | {| is_flat := true ; tactic := rkind (identity (partial cbv)) |}
       => time "identity cbv on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval cbv in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (identity (partial lazy)) |}
       => time "identity lazy on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval lazy in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (identity (partial simpl)) |}
       => time "identity simpl on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval simpl in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (identity (partial cbn)) |}
       => time "identity cbn on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval cbn in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (identity (full vm_compute)) |}
       => time "identity vm_compute on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval vm_compute in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (identity (full native_compute)) |}
       => time "identity native_compute on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval native_compute in ref_PHOAS) in idtac)
     | {| is_flat := true ; tactic := rkind (red_Denote cbv) |}
       => time "cbv Denote on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval cbv [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := true ; tactic := rkind (red_Denote lazy) |}
       => time "lazy Denote on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval lazy [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := true ; tactic := rkind (red_Denote cbn) |}
       => time "cbn Denote on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval cbn [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := true ; tactic := rkind (red_Denote simpl) |}
       => time "simpl Denote on PHOAS with big_flat-regression-quadratic" (idtac; let __ := (eval simpl in (PHOAS.Denote ref_PHOAS)) in idtac)

     | {| is_flat := false ; tactic := refine_let |}
       => time "refine let on PHOAS with big-regression-quadratic"
               (idtac; let p := fresh in refine (let p := ref_PHOAS in _))
     | {| is_flat := false ; tactic := transitivity |}
       => time "transitivity on PHOAS with big-regression-quadratic"
               (idtac;
                let p := fresh in
                assert (p : O = O);
                [ transitivity (Denote ref_PHOAS) | ])
     | {| is_flat := false ; tactic := rkind (identity (partial cbv)) |}
       => time "identity cbv on PHOAS with big-regression-quadratic" (idtac; let __ := (eval cbv in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (identity (partial lazy)) |}
       => time "identity lazy on PHOAS with big-regression-quadratic" (idtac; let __ := (eval lazy in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (identity (partial simpl)) |}
       => time "identity simpl on PHOAS with big-regression-quadratic" (idtac; let __ := (eval simpl in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (identity (partial cbn)) |}
       => time "identity cbn on PHOAS with big-regression-quadratic" (idtac; let __ := (eval cbn in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (identity (full vm_compute)) |}
       => time "identity vm_compute on PHOAS with big-regression-quadratic" (idtac; let __ := (eval vm_compute in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (identity (full native_compute)) |}
       => time "identity native_compute on PHOAS with big-regression-quadratic" (idtac; let __ := (eval native_compute in ref_PHOAS) in idtac)
     | {| is_flat := false ; tactic := rkind (red_Denote cbv) |}
       => time "cbv Denote on PHOAS with big-regression-quadratic" (idtac; let __ := (eval cbv [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := false ; tactic := rkind (red_Denote lazy) |}
       => time "lazy Denote on PHOAS with big-regression-quadratic" (idtac; let __ := (eval lazy [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := false ; tactic := rkind (red_Denote cbn) |}
       => time "cbn Denote on PHOAS with big-regression-quadratic" (idtac; let __ := (eval cbn [PHOAS.Denote PHOAS.denote] in (PHOAS.Denote ref_PHOAS)) in idtac)
     | {| is_flat := false ; tactic := rkind (red_Denote simpl) |}
       => time "simpl Denote on PHOAS with big-regression-quadratic" (idtac; let __ := (eval simpl in (PHOAS.Denote ref_PHOAS)) in idtac)
     | ?kind => fail 0 "Unrecognized kind:" kind
     end.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

partial_red_kind = ('cbv', 'lazy', 'simpl', 'cbn')
full_red_kind = ('vm_compute', 'native_compute')
red = ['partial ' + r for r in partial_red_kind] + ['full ' + r for r in full_red_kind]
red_kind = ['identity (%s)' % r for r in red] + ['red_Denote ' + r for r in partial_red_kind]
any_kind = ['rkind (%s)' % r for r in red_kind] + ['refine_let', 'transitivity']
for i, (is_flat, tactic) in enumerate([(is_flat, tactic) for is_flat in ('true', 'false') for tactic in any_kind]):
    kind = r'{| is_flat := %s ; tactic := %s |}' % (is_flat, tactic)
    print(f'Ltac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac run{i} sz := Harness.runtests (args_of_size {kind}) describe_goal mkgoal redgoal time_solve_goal{i} sz.\n')

>>>
 *)
Ltac time_solve_goal0 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (partial cbv)) |}).
Ltac run0 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (partial cbv)) |}) describe_goal mkgoal redgoal time_solve_goal0 sz.

Ltac time_solve_goal1 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (partial lazy)) |}).
Ltac run1 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (partial lazy)) |}) describe_goal mkgoal redgoal time_solve_goal1 sz.

Ltac time_solve_goal2 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (partial simpl)) |}).
Ltac run2 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (partial simpl)) |}) describe_goal mkgoal redgoal time_solve_goal2 sz.

Ltac time_solve_goal3 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (partial cbn)) |}).
Ltac run3 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (partial cbn)) |}) describe_goal mkgoal redgoal time_solve_goal3 sz.

Ltac time_solve_goal4 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (full vm_compute)) |}).
Ltac run4 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (full vm_compute)) |}) describe_goal mkgoal redgoal time_solve_goal4 sz.

Ltac time_solve_goal5 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (identity (full native_compute)) |}).
Ltac run5 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (identity (full native_compute)) |}) describe_goal mkgoal redgoal time_solve_goal5 sz.

Ltac time_solve_goal6 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (red_Denote cbv) |}).
Ltac run6 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (red_Denote cbv) |}) describe_goal mkgoal redgoal time_solve_goal6 sz.

Ltac time_solve_goal7 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (red_Denote lazy) |}).
Ltac run7 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (red_Denote lazy) |}) describe_goal mkgoal redgoal time_solve_goal7 sz.

Ltac time_solve_goal8 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (red_Denote simpl) |}).
Ltac run8 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (red_Denote simpl) |}) describe_goal mkgoal redgoal time_solve_goal8 sz.

Ltac time_solve_goal9 := time_solve_goal constr:({| is_flat := true ; tactic := rkind (red_Denote cbn) |}).
Ltac run9 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := rkind (red_Denote cbn) |}) describe_goal mkgoal redgoal time_solve_goal9 sz.

Ltac time_solve_goal10 := time_solve_goal constr:({| is_flat := true ; tactic := refine_let |}).
Ltac run10 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := refine_let |}) describe_goal mkgoal redgoal time_solve_goal10 sz.

Ltac time_solve_goal11 := time_solve_goal constr:({| is_flat := true ; tactic := transitivity |}).
Ltac run11 sz := Harness.runtests (args_of_size {| is_flat := true ; tactic := transitivity |}) describe_goal mkgoal redgoal time_solve_goal11 sz.

Ltac time_solve_goal12 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (partial cbv)) |}).
Ltac run12 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (partial cbv)) |}) describe_goal mkgoal redgoal time_solve_goal12 sz.

Ltac time_solve_goal13 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (partial lazy)) |}).
Ltac run13 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (partial lazy)) |}) describe_goal mkgoal redgoal time_solve_goal13 sz.

Ltac time_solve_goal14 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (partial simpl)) |}).
Ltac run14 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (partial simpl)) |}) describe_goal mkgoal redgoal time_solve_goal14 sz.

Ltac time_solve_goal15 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (partial cbn)) |}).
Ltac run15 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (partial cbn)) |}) describe_goal mkgoal redgoal time_solve_goal15 sz.

Ltac time_solve_goal16 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (full vm_compute)) |}).
Ltac run16 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (full vm_compute)) |}) describe_goal mkgoal redgoal time_solve_goal16 sz.

Ltac time_solve_goal17 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (identity (full native_compute)) |}).
Ltac run17 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (identity (full native_compute)) |}) describe_goal mkgoal redgoal time_solve_goal17 sz.

Ltac time_solve_goal18 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (red_Denote cbv) |}).
Ltac run18 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (red_Denote cbv) |}) describe_goal mkgoal redgoal time_solve_goal18 sz.

Ltac time_solve_goal19 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (red_Denote lazy) |}).
Ltac run19 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (red_Denote lazy) |}) describe_goal mkgoal redgoal time_solve_goal19 sz.

Ltac time_solve_goal20 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (red_Denote simpl) |}).
Ltac run20 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (red_Denote simpl) |}) describe_goal mkgoal redgoal time_solve_goal20 sz.

Ltac time_solve_goal21 := time_solve_goal constr:({| is_flat := false ; tactic := rkind (red_Denote cbn) |}).
Ltac run21 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := rkind (red_Denote cbn) |}) describe_goal mkgoal redgoal time_solve_goal21 sz.

Ltac time_solve_goal22 := time_solve_goal constr:({| is_flat := false ; tactic := refine_let |}).
Ltac run22 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := refine_let |}) describe_goal mkgoal redgoal time_solve_goal22 sz.

Ltac time_solve_goal23 := time_solve_goal constr:({| is_flat := false ; tactic := transitivity |}).
Ltac run23 sz := Harness.runtests (args_of_size {| is_flat := false ; tactic := transitivity |}) describe_goal mkgoal redgoal time_solve_goal23 sz.


Global Set NativeCompute Timing.
Global Open Scope N_scope.

(*
Goal True.
  run0 Sanity.
*)
