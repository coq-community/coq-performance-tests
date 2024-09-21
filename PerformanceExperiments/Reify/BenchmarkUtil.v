(** * Various utilities for benchmarking *)
From Coq Require Import NArith. (* for Pos.iter_op and Z.of_nat *)
Require Import Reify.Common.
Require Reify.PHOAS.
Require Import Reify.PHOASUtil.

(** ** Definition of the terms with which we build our benchmarking suite *)
Inductive count := none | one_more (how_many : count).
Fixpoint count_of_nat (v : nat) : count
  := match v with
     | O => none
     | S x => one_more (count_of_nat x)
     end.
Fixpoint nat_of_count (v : count) : nat
  := match v with
     | none => O
     | one_more x => S (nat_of_count x)
     end.

Fixpoint pos_of_succ_count (v : count) : positive
  := match v with
     | none => 1%positive
     | one_more x => Pos.succ (pos_of_succ_count x)
     end.
Definition N_of_count (v : count) : N
  := match v with
     | none => 0%N
     | one_more x => N.pos (pos_of_succ_count x)
     end.
Definition count_of_N (v : N) : count
  := count_of_nat (N.to_nat v).

Fixpoint big (x:nat) (n:count)
  : nat
  := match n with
     | none => x
     | one_more n'
       => dlet x' := x * x in
          big x' n'
     end.

Definition big_flat_op {T} (op : T -> T -> T) (a : T) (sz : count) : T
  := Eval cbv [N_of_count pos_of_succ_count Pos.iter_op Pos.succ] in
      match N_of_count sz with
      | N0 => a
      | Npos p => Pos.iter_op op p a
      end.
Definition big_flat (a : nat) (sz : count) : nat
  := big_flat_op Nat.mul a sz.

Ltac check_sane ref_PHOAS :=
  lazymatch goal with
  | [ |- _ = PHOAS.Denote ?e ]
    => let val := (eval vm_compute in (PHOAS.Beq e ref_PHOAS)) in
       lazymatch val with
       | true => idtac
       | false => idtac "Error: Got" e "Expected:" ref_PHOAS; unify e ref_PHOAS
       end
  | [ |- _ = PHOAS.denote ?e ]
    => let ref_HOAS := (eval lazy in (ref_PHOAS nat)) in
       let val := (eval vm_compute in (PHOAS.beq e ref_HOAS)) in
       lazymatch val with
       | true => idtac
       | false => idtac "Error: Got" e "Expected:" ref_HOAS; unify e ref_HOAS
       end
  | [ |- ?LHS = ?Denote ?e ]
    => let G := match goal with |- ?G => G end in
       fail 0 "Unrecognized denotation function" Denote "in goal" G
  | [ |- _ = ?v ]
    => let G := match goal with |- ?G => G end in
       fail 0 "Not an application of a denotation function to one argument:" v "in goal" G
  | [ |- ?G ]
    => fail 0 "Not an equality:" G
  end.
