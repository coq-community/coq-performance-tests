Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Strategy 100 [Let_In].

Global Instance Proper_Let_In_nd_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof. lazy; intros; subst; auto; congruence. Qed.
Global Instance Proper_Let_In_nd_changevalue_forall {A B} {RB:relation B}
  : Proper (eq ==> (forall_relation (fun _ => RB)) ==> RB) (Let_In (P:=fun _:A=>B)).
Proof. cbv; intuition (subst; eauto). Qed.
