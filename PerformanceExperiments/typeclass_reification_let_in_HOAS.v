(** We test memory usage of typeclass resification of let-binders to HOAS *)
Require Import PerformanceExperiments.Harness.
Generalizable All Variables.
Axiom Let_In : forall {A P} (v : A) (f : forall x : A, P x), P v.
Fixpoint nested_lets (n : nat) (init : nat) : nat
  := match n with
     | O => init + init
     | S n => Let_In (init + init) (fun x => nested_lets n x)
     end.

Inductive expr :=
| Zero
| Succ (n : expr)
| Plus (x y : expr)
| LetIn (x : expr) (f : nat -> expr)
| Var (v : nat)
.

Axiom P : expr -> Prop.
Axiom p : forall e, P e.

Class reified_of (v : nat) (e : expr) := dummy : True.
Hint Mode reified_of ! - : typeclass_instances.
Instance reify_plus {x ex y ey} {_:reified_of x ex} {_:reified_of y ey}
  : reified_of (x + y) (Plus ex ey) := I.
Instance reify_LetIn {x ex f ef} {_:reified_of x ex} {_:forall v ev, reified_of v (Var ev) -> reified_of (f v) (ef ev)}
  : reified_of (Let_In x f) (LetIn ex ef) := I.
Instance reify_0 : reified_of 0 Zero := I.
Instance reify_S {n en} {_:reified_of n en} : reified_of (S n) (Succ en) := I.
Definition reify (v : nat) {ev : expr} {_ : reified_of v ev} := ev.
Hint Extern 1 (reified_of _ ?ev) => progress cbv [ev] : typeclass_instances.
Hint Extern 0 (reified_of _ _) => progress cbv [nested_lets] : typeclass_instances.
Notation reified v := (match _ with e => match _ : reified_of v e with _ => e end end) (only parsing).

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  restart_timer;
  assert (P (reified (nested_lets n 0)));
  [ finish_timing ("Tactic call reify-regression-cubic");
    time "abstract-regression-linear" abstract apply p
  | ].

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => seq 1 100
     | Fast => List.map (fun x => x * 10) (seq 1 20)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. run0 Fast.
*)
