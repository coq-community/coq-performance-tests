(** Testing the performance of [pattern].  For not regressing on COQBUG(https://github.com/coq/coq/issues/11150) and COQBUG(https://github.com/coq/coq/issues/6502) *)
Definition Let_In {A P} (v : A) (f : forall x : A, P x) : P v
:= let x := v in f x.

Fixpoint big (a : nat) (sz : nat) : nat
  := match sz with
     | O => a
     | S sz' => Let_In (a * a) (fun a' => big a' sz')
     end.

Ltac do_time n :=
  try (
      once (assert (exists e, e = big 1 n);
            [ lazy -[big]; (*match goal with |- ?G => idtac G end;*) lazy [big];
              time pattern Nat.mul, S, O, (@Let_In nat (fun _ => nat))
            | ]);
      fail).

Local Set Warnings Append "-abstract-large-number".

Tactic Notation "do_n" tactic3(tac) := do 50 tac.

Goal True.
Proof.
  do_time 2; do_time 4; do_time 8; do_time 16; do_time 32; do_time 64;
    do_time 128; do_time 256; do_time 512.
  idtac 1024; do_n do_time 1024.
  idtac 2048; do_n do_time 2048.
  idtac 4096; do_n do_time 4096.
  idtac 8192; do_n do_time 8192.
  idtac 16384; do_n do_time 16384.
  exact I.
Defined.
