(** We test memory usage of typeclass resification of let-binders to HOAS *)
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

Time Definition foo10 : P (reified (nested_lets 10 0)). Time apply p. Time Qed.
Time Definition foo50 : P (reified (nested_lets 50 0)). Time apply p. Time Qed.
Time Definition foo100 : P (reified (nested_lets 100 0)). Time apply p. Time Qed.
Time Definition foo150 : P (reified (nested_lets 150 0)). Time apply p. Time Qed.
Time Definition foo200 : P (reified (nested_lets 200 0)). Time apply p. Time Qed.
