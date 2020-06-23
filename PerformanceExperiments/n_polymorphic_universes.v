Require Import Coq.ZArith.ZArith.
Require Import PerformanceExperiments.Harness.
Global Open Scope Z_scope.
Set Universe Polymorphism.
Record prod A B := pair { fst : A ; snd : B }.

Ltac make n base :=
  lazymatch n with
  | S ?n => let v := make n base in
            uconstr:(prod v v)
  | O => base
  end.

Global Set Warnings Append "-abstract-large-number".

Ltac mkgoal _ := constr:(True).
Ltac redgoal _ := idtac.
Ltac describe_goal n :=
  let n := (eval cbv in (Z.of_nat n)) in
  let pow2n := (eval cbv in (Z.pow 2 n)) in
  idtac "Params: 0-univ-count=" pow2n ", 1-n=" n.
Ltac time_solve_goal0 n :=
  assert_succeeds assert Type by
    time "abstract-regression-quadratic-regression-cubic"
         transparent_abstract
         (let v := make n uconstr:(Type) in
          cut True;
          [ intros _;
            time "exact-regression-quadratic-regression-cubic-regression-linear" exact v
          | restart_timer; exact I ]);
  finish_timing ( "Tactic call close-abstract-regression-quadratic-regression-cubic" ).

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 5
     | Fast => seq 0 15
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. Time run0 Fast.
*)
