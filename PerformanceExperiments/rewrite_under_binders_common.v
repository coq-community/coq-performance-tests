(** * performance of rewrite/rewrite_strat under binders *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Module Type LetInT.
  Parameter Let_In : forall {A P} (x : A) (f : forall a : A, P a), P x.
  Axiom Let_In_def : @Let_In = fun A P x f => let y := x in f y.
  (*
  Global Strategy 100 [Let_In].
  Hint Opaque Let_In : rewrite.
   *)
  Reserved Notation "'dlet_nd' x .. y := v 'in' f"
           (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
  Reserved Notation "'dlet' x .. y := v 'in' f"
           (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
  Notation "'dlet_nd' x .. y := v 'in' f" := (Let_In (P:=fun _ => _) v (fun x => .. (fun y => f) .. )) (only parsing).
  Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
  Axiom Let_In_nd_Proper : forall {A P},
      Proper (eq ==> pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => P)).
  Hint Extern 0 (Proper _ (@Let_In _ _)) => simple apply @Let_In_nd_Proper : typeclass_instances.
End LetInT.

Module Export LetIn : LetInT.
  Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x
    := let y := x in f y.
  Lemma Let_In_def : @Let_In = fun A P x f => let y := x in f y.
  Proof. reflexivity. Qed.
  Global Strategy 100 [Let_In].
  Hint Opaque Let_In : rewrite.
  Global Instance Let_In_nd_Proper {A P}
    : Proper (eq ==> pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => P)).
  Proof. cbv; intros; subst; auto. Qed.
End LetIn.

Global Instance eq_eq_eq {A}
  : Proper (eq ==> eq ==> eq) (@eq A).
Proof. repeat intro; subst; reflexivity. Qed.
Global Instance all_Proper {A} (* Why do we need this??? *)
  : Proper (pointwise_relation _ eq ==> Basics.flip Basics.impl) (@all A).
Proof. intros f g H Hg x; specialize (H x); specialize (Hg x); congruence. Qed.

Fixpoint make_lets_def (n : nat) (v : nat) (acc : nat) {struct n} :=
  match n with
  | 0 => acc + acc + v
  | S n => dlet acc := acc + acc + v in make_lets_def n v acc
  end.

Fixpoint make_lets_noop_def (n : nat) (acc : nat) {struct n} :=
  match n with
  | 0 => acc + acc
  | S n => dlet acc := acc + acc in make_lets_noop_def n acc
  end.

Notation goal n := (forall acc, make_lets_def n 0 acc = acc) (only parsing).
Notation goal_noop n := (forall acc, make_lets_noop_def n acc = acc) (only parsing).

Ltac mkgoal n := constr:(goal n).
Ltac mkgoal_noop n := constr:(goal_noop n).
Ltac redgoal _ := cbv [make_lets_def make_lets_noop_def].
