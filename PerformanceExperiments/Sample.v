(** Utility file for subsampling large distributions *)
Require Import Coq.Structures.Orders.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.QArith.QArith Coq.QArith.Qround Coq.QArith.Qabs Coq.QArith.Qminmax.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Definition extra_fuel : nat := 100%nat.

Module QOrder <: TotalLeBool.
  Local Open Scope Q_scope.
  Local Open Scope Z_scope.
  Definition t := Q.
  Definition leb : t -> t -> bool := Qle_bool.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb]; intros a1 a2; rewrite !Qle_bool_iff.
    cbv [Qle Qnum Qden]; destruct a1, a2; lia.
  Qed.
End QOrder.

Module QSort := Sort QOrder.
Local Notation sort := QSort.sort.

Module NatIndexOrder (Order : TotalLeBool) <: TotalLeBool.
  Definition t := (nat * Order.t)%type.
  Definition leb : t -> t -> bool := fun '(_, x) '(_, y) => Order.leb x y.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb]; intros [_ a1] [_ a2]; apply Order.leb_total.
  Qed.
End NatIndexOrder.

Module NatIndexQOrder := NatIndexOrder QOrder.
Module NatIndexQSort := Sort NatIndexQOrder.

Definition sort_by {T} (size : T -> Q) (ls : list T) : list T
  := match ls with
     | nil => nil
     | default :: _
       => List.map (fun '(idx, _) => nth idx ls default)
                   (NatIndexQSort.sort (List.combine (seq 0 (length ls))
                                                     (List.map size ls)))
     end.

Fixpoint cumulate (from : Q) (ls : list Q) : list Q
  := match ls with
     | [] => []
     | x :: xs
       => let from := (from + Qmax 0 x)%Q in
          from :: cumulate from xs
     end.

Definition make_cumulants {T} (size : T -> Q) (ls : list T) : list (T * Q)
  := List.combine ls (cumulate 0 (List.map size ls)).

(** Allocate 1/n of the allocation to each 1/n of the elements in the list *)
Fixpoint binary_alloc_fueled {T} (size : T -> Q) (allocation : Q) (ls : list T) (fuel : nat) : list T
  := match fuel with
     | O => ls
     | S fuel
       => let cumulants := make_cumulants size ls in
          let total := hd 0%Q (List.map (@snd _ _) (List.rev cumulants)) in
          if Qle_bool total allocation
          then ls
          else
            let '(ls1, ls2) := List.partition (fun '(_, so_far) => Qle_bool so_far (total / 2)) cumulants in
            match ls1, ls2 with
            | [], [] => []
            | [], lsc
            | lsc, []
              => List.map (@fst _ _) (List.filter (fun '(_, so_far) => Qle_bool so_far allocation) lsc)
            | _ :: _, (x, _) :: _
              => if Qle_bool (size x) (allocation / 2)
                 then
                   let ls2 := binary_alloc_fueled size (allocation / 2) (List.map (@fst _ _) ls2) fuel in
                   let ls2_total := List.fold_right Qplus 0%Q (List.map (Qmax 0) (List.map size ls2)) in
                   let ls1 := binary_alloc_fueled size (allocation - ls2_total) (List.map (@fst _ _) ls1) fuel in
                   ls1 ++ ls2
                 else
                   if Qle_bool (size x) allocation
                   then
                     let ls1 := binary_alloc_fueled size (allocation - size x) (List.map (@fst _ _) ls1) fuel in
                     ls1 ++ [x]
                   else
                     List.map (@fst _ _) (List.filter (fun '(_, so_far) => Qle_bool so_far allocation) ls1)
            end
     end.

Definition binary_alloc {T} (size : T -> Q) (allocation : Q) (ls : list T) : list T
  := binary_alloc_fueled size allocation ls (S (length ls)).

Definition sort_by_size_and_alloc {T} (size : T -> Q) (allocation : Q) (ls : list T) : list T
  := binary_alloc size allocation (sort_by size ls).

Fixpoint find_above_max_size {T} (double : T -> T) (size : T -> Q) (max_size : Q) (ndoublings : nat) (t_prev t_cur : T) (fuel : nat) : T * T * nat (* ndoublings *)
  := match fuel with
     | O => (t_prev, t_cur, ndoublings)
     | S fuel
       => if Qle_bool max_size (size t_cur)
          then (t_prev, t_cur, ndoublings)
          else find_above_max_size double size max_size (S ndoublings) t_cur (double t_cur) fuel
     end.

Fixpoint find_just_below_max_size {T} (avg : T -> T -> T) (size : T -> Q) (max_size : Q) (t_lo t_hi : T) (fuel : nat) : T
  := match fuel with
     | O => t_lo
     | S fuel
       => let sz_lo := size t_lo in
          let sz_hi := size t_hi in
          if Qeq_bool sz_lo sz_hi
          then t_lo
          else let t_mid := avg t_lo t_hi in
               let sz_mid := size t_mid in
               let '(t_lo, t_hi) :=
                   if Qle_bool max_size sz_mid
                   then (t_lo, t_mid)
                   else (t_mid, t_hi) in
               find_just_below_max_size avg size max_size t_lo t_hi fuel
     end.

Definition find_max {T} (double : T -> T) (avg : T -> T -> T) (size : T -> Q) (max_size : Q) (init : T) : T
  := let '(t_lo, t_hi, ndoublings) := find_above_max_size double size max_size 0 init init (extra_fuel + Z.to_nat (Qceiling max_size)) in
     find_just_below_max_size avg size max_size t_lo t_hi (extra_fuel + Nat.pow 2 (pred ndoublings)).

Class has_double_avg T := { double_T : T -> T ; avg_T : T -> T -> T }.
Class has_generate T := { generate_from_to_T : T -> T -> list T }.

Global Instance nat_has_double_avg : has_double_avg nat
  := { double_T := Nat.mul 2 ; avg_T x y := ((x + y) / 2)%nat }.

Global Instance N_has_double_avg : has_double_avg N
  := { double_T := N.mul 2 ; avg_T x y := ((x + y) / 2)%N }.

Global Instance Z_has_double_avg : has_double_avg Z
  := { double_T := Z.mul 2 ; avg_T x y := ((x + y) / 2)%Z }.

Definition nat_prod_has_double_avg : has_double_avg (nat * nat)
  := let make v := (Nat.sqrt v, Nat.sqrt_up v) in
     {| double_T := fun '(x, y) => make (2 * x * y)%nat
        ; avg_T := fun '(x, y) '(x', y') => make ((x * y + x' * y') / 2)%nat |}.

Definition N_prod_has_double_avg : has_double_avg (N * N)
  := let make v := (N.sqrt v, N.sqrt_up v) in
     {| double_T := fun '(x, y) => make (2 * x * y)%N
        ; avg_T := fun '(x, y) '(x', y') => make ((x * y + x' * y') / 2)%N |}.

Definition Z_prod_has_double_avg : has_double_avg (Z * Z)
  := let make v := (Z.sqrt v, Z.sqrt_up v) in
     {| double_T := fun '(x, y) => make (2 * x * y)%Z
        ; avg_T := fun '(x, y) '(x', y') => make ((x * y + x' * y') / 2)%Z |}.

Global Instance nat_has_generate : has_generate nat
  := { generate_from_to_T from to := seq from (S (to - from)) }.

Global Instance N_has_generate : has_generate N
  := { generate_from_to_T from to := List.map N.of_nat (seq (N.to_nat from) (S (N.to_nat (to - from)))) }.

Global Instance Z_has_generate : has_generate Z
  := { generate_from_to_T from to := List.map Z.of_nat (seq (Z.to_nat from) (S (Z.to_nat (to - from)))) }.

Definition N_prod_has_generate : has_generate (N * N)
  := {| generate_from_to_T from to
        := (let from := fst from * snd from in
            let to := fst to * snd to in
            List.flat_map
              (fun n => List.map (fun m => (n, m))
                                 (generate_from_to_T ((from + (n - 1)) / n) (to / n)))
              (generate_from_to_T from to))%N |}.

Definition nat_prod_has_generate : has_generate (nat * nat)
  := let __ := N_prod_has_generate in
     let to_pair_N := fun '(x, y) => (N.of_nat x, N.of_nat y) in
     let of_pair_N := fun '(x, y) => (N.to_nat x, N.to_nat y) in
     {| generate_from_to_T from to := List.map of_pair_N (generate_from_to_T (to_pair_N from) (to_pair_N to)) |}.

Definition Z_prod_has_generate : has_generate (Z * Z)
  := let __ := N_prod_has_generate in
     let to_pair_N := fun '(x, y) => (Z.to_N x, Z.to_N y) in
     let of_pair_N := fun '(x, y) => (Z.of_N x, Z.of_N y) in
     {| generate_from_to_T from to := List.map of_pair_N (generate_from_to_T (to_pair_N from) (to_pair_N to)) |}.

Definition generate_inputs
           {T} {_ : has_double_avg T} {_ : has_generate T}
           (init : T)
           (size : T -> Q)
           (allocation : Q)
           (max_size : Q)
  : list T
  := let max := find_max double_T avg_T size max_size init in
     sort_by_size_and_alloc size allocation (generate_from_to_T init max).
