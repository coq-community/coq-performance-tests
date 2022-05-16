(** We test memory usage of typeclass resification of let-binders to HOAS *)
Require Import PerformanceExperiments.Harness.
Generalizable All Variables.
Axiom Let_In : forall {A P} (v : A) (f : forall x : A, P x), P v.
Fixpoint nested_lets (n : nat) (init : nat) : nat
  := match n with
     | O => init + init
     | S n => Let_In (init + init) (fun x => nested_lets n x)
     end.

Inductive type := NAT.
Inductive expr {var : type -> Type} : type -> Type :=
| Zero : expr NAT
| Succ (n : expr NAT) : expr NAT
| Plus (x y : expr NAT) : expr NAT
| LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
| Var {T} (v : var T) : expr T
.

Axiom P : forall {var t}, @expr var t -> Prop.
Axiom p : forall var t e, @P var t e.
Ltac solve_P := intros; apply p.

Class type_reified_of (v : Type) (t : type) := dummyT : True.
#[global]
Typeclasses Opaque type_reified_of.
#[global]
Hint Mode type_reified_of ! - : typeclass_instances.
#[global]
Instance reify_nat : type_reified_of nat NAT := I.
Class reified_of {var A B} (v : A) (e : @expr var B) := dummy : True.
#[global]
Typeclasses Opaque reified_of.
#[global]
Typeclasses Opaque Nat.add.
#[global]
Hint Mode reified_of - - - ! - : typeclass_instances.
#[global]
Instance reify_plus {var x ex y ey} {_:reified_of x ex} {_:reified_of y ey}
  : reified_of (x + y) (@Plus var ex ey) := I.
#[global]
Instance reify_LetIn {var A B tA tB x ex f ef} {_:reified_of x ex} {_:forall v ev, reified_of v (Var ev) -> reified_of (f v) (ef ev)}
  : reified_of (@Let_In A (fun _ => B) x f) (@LetIn var tA tB ex ef) := I.
#[global]
Instance reify_0 {var} : reified_of 0 (@Zero var) := I.
#[global]
Instance reify_S {var n en} {_:reified_of n en} : reified_of (S n) (@Succ var en) := I.
Definition reify {var T T'} (v : T) {ev : @expr var T'} {_ : reified_of v ev} := ev.
Ltac subst_evars :=
  repeat match goal with
         | [ x := ?e |- _ ] => is_evar e; subst x
         end.
#[global]
Hint Extern 0 (reified_of _ _) => progress (cbv [nested_lets]; subst_evars) : typeclass_instances.

Notation reified var' v := (match _ return _ with t => match _ : @expr var' t return _ with e => match _ : reified_of v e with _ => e end end end) (only parsing).

Notation goal n := (forall var, P (reified var (nested_lets n 0))) (only parsing).

Ltac mkgoal n := constr:(True).
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  restart_timer;
  assert (goal n);
  [ finish_timing ("Tactic call reify-regression-cubic");
    time "abstract-regression-linear" abstract solve_P
  | ].

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 1 3
     | SuperFast => seq 1 100
     | Fast => (List.map (fun x => x * 10) (seq 1 30))
                 ++ (List.map (fun x => x * 50) (seq 1 10))
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True. run0 Fast.
*)
