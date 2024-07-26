From Coq Require Import ZArith.
Local Open Scope Z_scope.
Set Universe Polymorphism.
Record prod A B := pair { fst : A ; snd : B }.

Ltac make n base :=
  lazymatch n with
  | S ?n => let v := make n base in
            uconstr:(prod v v)
  | O => base
  end.

Ltac test n :=
  let zn := (eval cbv in (Z.of_nat n)) in
  let z2n := (eval cbv in (Z.pow 2 zn)) in
  idtac "n=" zn ", univ_count=" z2n;
  assert_succeeds assert Type by
      time "abstract" (let v := make n uconstr:(Type) in
                       transparent_abstract time "exact" exact v).

Ltac iter_test up_to :=
  let up_to := lazymatch type of up_to with
               | nat => up_to
               | Z => (eval cbv in (Z.to_nat up_to))
               end in
  lazymatch up_to with
  | O => idtac
  | S ?n => iter_test n
  end;
  test up_to.

Goal True. iter_test 14. Abort.
(* n= 0 , univ_count= 1
Tactic call exact ran for 0. secs (0.u,0.s) (success)
Tactic call abstract ran for 0. secs (0.u,0.s) (success)
n= 1 , univ_count= 2
Tactic call exact ran for 0. secs (0.u,0.s) (success)
Tactic call abstract ran for 0. secs (0.u,0.s) (success)
n= 2 , univ_count= 4
Tactic call exact ran for 0. secs (0.u,0.s) (success)
Tactic call abstract ran for 0. secs (0.u,0.s) (success)
n= 3 , univ_count= 8
Tactic call exact ran for 0. secs (0.u,0.s) (success)
Tactic call abstract ran for 0. secs (0.u,0.s) (success)
n= 4 , univ_count= 16
Tactic call exact ran for 0. secs (0.u,0.s) (success)
Tactic call abstract ran for 0.001 secs (0.u,0.001s) (success)
n= 5 , univ_count= 32
Tactic call exact ran for 0.001 secs (0.001u,0.s) (success)
Tactic call abstract ran for 0.003 secs (0.003u,0.s) (success)
n= 6 , univ_count= 64
Tactic call exact ran for 0.002 secs (0.002u,0.s) (success)
Tactic call abstract ran for 0.006 secs (0.006u,0.s) (success)
n= 7 , univ_count= 128
Tactic call exact ran for 0.004 secs (0.004u,0.s) (success)
Tactic call abstract ran for 0.016 secs (0.016u,0.s) (success)
n= 8 , univ_count= 256
Tactic call exact ran for 0.008 secs (0.008u,0.s) (success)
Tactic call abstract ran for 0.033 secs (0.033u,0.s) (success)
n= 9 , univ_count= 512
Tactic call exact ran for 0.016 secs (0.016u,0.s) (success)
Tactic call abstract ran for 0.082 secs (0.082u,0.s) (success)
n= 10 , univ_count= 1024
Tactic call exact ran for 0.032 secs (0.032u,0.s) (success)
Tactic call abstract ran for 0.22 secs (0.22u,0.s) (success)
n= 11 , univ_count= 2048
Tactic call exact ran for 0.067 secs (0.067u,0.s) (success)
Tactic call abstract ran for 0.639 secs (0.639u,0.s) (success)
n= 12 , univ_count= 4096
Tactic call exact ran for 0.161 secs (0.161u,0.s) (success)
Tactic call abstract ran for 2.202 secs (2.202u,0.s) (success)
n= 13 , univ_count= 8192
Tactic call exact ran for 0.382 secs (0.382u,0.s) (success)
Tactic call abstract ran for 7.89 secs (7.89u,0.s) (success)
n= 14 , univ_count= 16384
Tactic call exact ran for 0.813 secs (0.813u,0.s) (success)
Tactic call abstract ran for 29.435 secs (29.418u,0.016s) (success)
*)
