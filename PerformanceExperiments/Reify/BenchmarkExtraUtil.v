Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import PerformanceExperiments.Sandbox.
Require Import Reify.ReifyCommon.
Require Import Reify.PHOASUtil.
Require Export Reify.BenchmarkUtil. (* don't qualify BenchmarkUtil.big when naming it *)
Require PerformanceExperiments.Harness.
Require Reify.ParametricityCommon.
Local Open Scope N_scope.
Local Open Scope list_scope.

Local Coercion N.of_nat : nat >-> N.

Definition sequence : list N
  := Eval lazy in
      let m := List.map N.of_nat in
      (m (List.seq 1 499))
        ++ (List.map (fun n : nat => 500 + n * 5) (seq 0 100))
        ++ (List.map (fun n : nat => 1000 + n * 10) (seq 0 100))
        ++ (List.map (fun n : nat => 2 * 1000 + n * 50) (seq 0 160))
        ++ (List.map (fun n : nat => 10 * 1000 + n * 100) (seq 0 100))
        ++ 200 * 100::nil.

Definition args_of_max_n (max_n : N) : list N
  := List.filter (fun v => N.leb v max_n) sequence.

Definition rbig (n : count) (var : Type) :=
  Eval cbv beta in
    ltac:(let v := (eval lazy delta [big] in (big 1 n)) in
          let rv := ParametricityCommon.reify var v in
          exact rv).

Definition rbig_flat (n : count) (var : Type) :=
  Eval cbv beta in
    ltac:(let v := (eval lazy [big_flat] in (big_flat 1 n)) in
          let rv := ParametricityCommon.reify var v in
          exact rv).

Ltac mkgoal is_flat :=
  let n_to_count n := (eval lazy in (count_of_N n)) in
  lazymatch (eval cbv in is_flat) with
  | true => fun n => let n := n_to_count n in constr:(exists v, v = big_flat 1 n)
  | false => fun n => let n := n_to_count n in constr:(exists v, v = big 1 n)
  | ?v => fail 0 "Invalid argument for is_flat (expected true or false):" v
  end.
Ltac red_goal _ := idtac.
Ltac time_solve_goal do_cbv pre_reify do_reify post_reify n :=
  eexists;
  once (do_cbv n);
  once (pre_reify n);
  once (do_reify n);
  once (post_reify n).
Ltac do_verify is_flat :=
  let ref_PHOAS := lazymatch (eval cbv in is_flat) with
                   | true => fun n => (eval lazy in (rbig_flat (count_of_N n)))
                   | false => fun n => (eval lazy in (rbig (count_of_N n)))
                   | ?v => fail 0 "Invalid argument for is_flat (expected true or false):" v
                   end in
  fun n => check_sane ltac:(ref_PHOAS n).

Ltac noop _ := idtac.
Ltac do_cbv_delta _ := lazy [big_flat count_of_nat]; lazy delta [big].
Ltac do_cbv _ := lazy [big_flat big big_flat_op count_of_nat].

Definition do_trans_of_size (sz : Harness.size)
  := match sz with
     | Harness.Sanity => true
     | _ => false
     end.
