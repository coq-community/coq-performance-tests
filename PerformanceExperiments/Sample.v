(** Utility file for subsampling large distributions *)
Require Import Coq.Structures.Orders.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.QArith.QArith Coq.QArith.Qround Coq.QArith.Qabs Coq.QArith.Qminmax.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Definition extra_fuel : nat := 100%nat.
Definition cutoff_elem_count := 3%N.

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

Local Coercion N.of_nat : nat >-> N.
Local Coercion Z.of_N : N >-> Z.
Local Coercion inject_Z : Z >-> Q.
Local Coercion Npos : positive >-> N.

(** Allocate 1/n time to each 1/n of the codomain *)
Fixpoint binary_alloc_QT_fueled
         {T} {_ : has_double_avg T}
         (size : T -> Q)
         (count_elems : forall min max : T, N)
         (total_time_all_elems : forall min max : T, Q)
         (allocation : Q)
         (min : T) (max : T)
         (cutoff_elem_count : N)
         (fuel : nat)
  : list ((T * T (* min * max *)) * N) * Q (* allocation used *)
  := let allocation := Qmax 0 allocation in
     match fuel with
     | O => (nil, 0)
     | S fuel
       => if (count_elems min max =? 0)%N
          then (nil, 0)
          else
            let time_per_elem := total_time_all_elems min max / count_elems min max in
            let n_elem := Z.to_N (Qfloor (allocation / time_per_elem)) in
            if (n_elem =? 0)%N
            then (nil, 0)
            else
              if (n_elem <=? cutoff_elem_count)%N
              then ([((min, max), n_elem)], time_per_elem * n_elem)
              else
                let mid := avg_T min max in
                let '(min_sz, mid_sz, max_sz) := (size min, size mid, size max) in
                if Qeq_bool min_sz max_sz || Qeq_bool min_sz mid_sz || Qeq_bool mid_sz max_sz
                then
                  ([((min, max), n_elem)], time_per_elem * n_elem)
                else
                  let alloc_hi := allocation * (max_sz - mid_sz) / (max_sz - min_sz) in
                  let '(ret_hi, alloc_hi) := binary_alloc_QT_fueled size count_elems total_time_all_elems alloc_hi mid max cutoff_elem_count fuel in
                let '(ret_lo, alloc_lo) := binary_alloc_QT_fueled size count_elems total_time_all_elems (allocation - alloc_hi) min mid cutoff_elem_count fuel in
                (ret_lo ++ ret_hi, alloc_lo + alloc_hi)
     end.

Definition binary_alloc
           {T} {_ : has_double_avg T}
           (size : T -> Q)
           (count_elems : forall min max : T, N)
           (total_time_all_elems : forall min max : T, Q)
           (allocation : Q)
           (min : T) (max : T)
           (cutoff_elem_count : N)
           (alloc : forall min max : T, N -> list T)
  : list T
  := List.flat_map
       (fun '((min, max), n) => alloc min max n)
       (fst (binary_alloc_QT_fueled size count_elems total_time_all_elems allocation min max cutoff_elem_count (100 + N.to_nat (N.log2_up (count_elems min max))))).

Class has_count T :=
  { count_elems_T : forall min max : T, N }.

Class has_alloc T :=
  { alloc_T : forall min max : T, N -> list T }.

Class has_size T := size_T : T -> Q.

Class has_total_time T :=
  total_time_all_elems_T : forall min max : T, Q.

Definition generate_inputs
           {T} {_ : has_double_avg T} {_ : has_count T} {_ : has_alloc T}
           (init : T)
           (size : has_size T)
           {_ : let _ := size in has_total_time T}
           (allocation : Q)
           (max_size : Q)
  : list T
  := let max := find_max double_T avg_T size max_size init in
     binary_alloc size count_elems_T total_time_all_elems_T allocation init max cutoff_elem_count alloc_T.

Global Instance Q_has_alloc : has_alloc Q
  := { alloc_T min max n
       := let step := (max - min) / (n - 1) in
          List.map (fun i:nat => min + i * step) (seq 0 (N.to_nat n)) }.

Global Instance Z_has_count : has_count Z
  := { count_elems_T min max
       := Z.to_N (1 + max - min) }.

Global Instance N_has_count : has_count N
  := { count_elems_T min max := count_elems_T (min:Z) (max:Z) }.

Global Instance nat_has_count : has_count nat
  := { count_elems_T min max := count_elems_T (min:N) (max:N) }.

Global Instance Z_has_alloc : has_alloc Z
  := { alloc_T min max n
       := List.map (fun v:Q => Qfloor (1/2 + v)) (alloc_T (min:Q) (max:Q) n) }.

Global Instance N_has_alloc : has_alloc N
  := { alloc_T min max n := List.map Z.to_N (alloc_T (min:Z) (max:Z) n) }.

Global Instance nat_has_alloc : has_alloc nat
  := { alloc_T min max n := List.map N.to_nat (alloc_T (min:N) (max:N) n) }.

Definition op_from_to {T} (op : T -> T -> T) (id : T)
           (lower upper : Z) (f : Z -> T) : T
  := List.fold_right op
                     id
                     (List.map (fun x:nat => f (lower + x)%Z) (seq 0 (1 + Z.to_nat (upper - lower)))).

Definition Zprod_from_to (lower upper : Z) (f : Z -> Z) : Z
  := op_from_to Z.mul 1%Z lower upper f.
Definition Zsum_from_to (lower upper : Z) (f : Z -> Z) : Z
  := op_from_to Z.add 0%Z lower upper f.

Local Notation "'Π_{' x = lower '}^{' upper } f"
  := (Zprod_from_to lower upper (fun x => f))
       (x ident, at level 35) : Z_scope.
Local Notation "'∑_{' x = lower '}^{' upper } f"
  := (Zsum_from_to lower upper (fun x => f))
       (x ident, at level 35) : Z_scope.

Fixpoint group_by' {T} (eqb : T -> T -> bool) (ls : list T) (acc : list T) {struct ls}
  : list (list T)
  := match ls, acc with
     | [], [] => []
     | [], acc => [List.rev acc]
     | x::xs, [] => group_by' eqb xs [x]
     | x::xs, y::_ => if eqb x y
                      then group_by' eqb xs (x::acc)
                      else acc :: group_by' eqb xs [x]
     end.

Definition group_by {T} (eqb : T -> T -> bool) (ls : list T)
  := group_by' eqb ls [].

Global Instance Z_prod_has_count : has_count (Z * Z)
  := { count_elems_T min max
       := (let min := fst min * snd min in
           let max := fst max * snd max in
           (*∑_{i=1}^max ∑_{j=min/i}^{max/i} 1*)
           (*∑_{i=1}^max 1 + ⌊max/i⌋-⌈min/i⌉ *)
           Z.to_N (∑_{i=1}^{max} (1 + Qfloor (max/i) + Qceiling (min/i))))%Z }.

Global Instance N_prod_has_count : has_count (N * N)
  := { count_elems_T '(x1, x2) '(y1, y2) := count_elems_T (x1:Z, x2:Z) (y1:Z, y2:Z) }.

Global Instance nat_prod_has_count : has_count (nat * nat)
  := { count_elems_T '(x1, x2) '(y1, y2) := count_elems_T (x1:N, x2:N) (y1:N, y2:N) }.

Definition Qsqrt_up (v : Q) : Q
  := Z.sqrt_up (Qnum v) # (Z.to_pos (Z.sqrt (Qden v))).
Definition Qsqrt (v : Q) : Q
  := Z.sqrt (Qnum v) # (Z.to_pos (Z.sqrt_up (Qden v))).

Fixpoint take_uniform_n' {T} (ls : list T) (len : nat) (n : nat) : list T
  := match n, ls, List.rev ls with
     | 0%nat, _, _ => []
     | _, [], _ => []
     | _, _, [] => []
     | 1%nat, x::_, _ => [x]
     | 2%nat, [x], _ => [x]
     | 2%nat, x::_, y::_ => [x; y]
     | S n', x::xs, _
       => let skip := Z.to_nat (Qfloor (1/2 + len / n - 1)) in
          x :: take_uniform_n' (skipn skip xs) (len - 1 - skip) n'
     end.

Definition take_uniform_n {T} ls n := @take_uniform_n' T ls (List.length ls) n.

Global Instance Z_prod_has_alloc : has_alloc (Z * Z)
  := { alloc_T min max n
       := match n with
          | 0%N => []
          | 1%N => [max]
          | 2%N => [min; max]
          | _
            => (let min := fst min * snd min in
                let max := fst max * snd max in
                List.flat_map
                  (fun vals
                   => match vals with
                      | v::_
                        => let n := List.length vals in
                           let min := Z.sqrt v in
                           let max := Z.sqrt_up v in
                           List.flat_map
                             _
                             (alloc_T min max n)
                      | [] => []
                      end)
                  (group_by Z.eqb (alloc_T min max n)))%Z
          end }.



Global Instance Z_prod_has_alloc : has_count_alloc (Z * Z)
  := { count_elems_T min max
       := (let min := fst min * snd min in
           let max := fst max * snd max in
           (*∑_{i=1}^max ∑_{j=min/i}^{max/i} 1*)
           (*∑_{i=1}^max 1 + ⌊max/i⌋-⌈min/i⌉ *)
           Z.to_N (∑_{i=1}^{max} (1 + Qfloor (max/i) + Qceiling (min/i))))%Z
       ; alloc_T min max n
         := match n with
            | 0%N => []
            | 1%N => [max]
            | 2%N => [min; max]
            | _
              => (let min := fst min * snd min in
                  let max := fst max * snd max in
                  List.flat_map
                    (fun vals
                     => match vals with
                        | v::_
                          => let n := List.length vals in
                             let min := Z.sqrt v in
                             let max := Z.sqrt_up v in
                             List.flat_map
                               _
                               (alloc_T min max n)
                        | [] => []
                        end)
                    (group_by Z.eqb (alloc_T min max n)))%Z
            end }.


            then []
            else
              if (n =?(
             let step := (max - min) / (n - 1) in
            List.map (fun i:nat => Qfloor (min + 1/2 + i * step)) (seq 0 (N.to_nat n))
Definition N_prod_has_generate : has_generate (N * N)
  := {| generate_from_to_T from to
        := (let from := fst from * snd from in
            let to := fst to * snd to in
            List.flat_map
              (fun n => List.map (fun m => (n, m))
                                 (generate_from_to_T ((from + (n - 1)) / n) (to / n)))
              (generate_from_to_T from to))%N |}.



Global Instance N_has_count_alloc : has_count_alloc N
  := { count_elems_T min max := count_elems_T (min:Z) (max:Z)
       ; alloc_T min max n := List.map Z.to_N (alloc_T (min:Z) (max:Z) n) }.

Global Instance nat_has_count_alloc : has_count_alloc nat
  := { count_elems_T min max := count_elems_T (min:N) (max:N)
       ; alloc_T min max n := List.map N.to_nat (alloc_T (min:N) (max:N) n) }.

Definition polynomial := list (Q * Z) (* coef, exp *).

Definition integrate_poly (p : polynomial) : polynomial * Q (* logarithmic factor *)
  := (List.flat_map (fun '(coeff, exp) => if negb (exp =? -1)%Z
                                          then [(coeff / (exp + 1)%Z, (exp + 1)%Z)]
                                          else [])
                    p,
      List.fold_right
        (fun x y => x + y)%Q
        0%Q
        (List.map (fun '(coeff, exp) => if (exp =? -1)%Z then coeff else 0%Q) p)).
Definition diff_poly (p : polynomial) : polynomial
  := List.map (fun '(coeff, exp) => (coeff * (exp:Z), (exp - 1)%Z)) p.

Definition eval_poly (p : polynomial) (x : Q) : Q
  := List.fold_right (fun x y => x + y)%Q 0%Q
                     (List.map (fun '(coeff, exp) => coeff * Qpower x exp) p).

Inductive known_poly :=
| constant (c : Q)
| linear (m b : Q)
| quadratic (a b c : Q)
| cubic (a b c d : Q)
| quartic (a b c d e : Q)
| quintic (a b c d e f : Q)
.

Inductive known_equation :=
| poly (p : known_poly)
| logarithmic (a b : Q) (* a ln(b x) *)
| exponential (a b : Q) (* a exp(b x) *)
.

Coercion poly : known_poly >-> known_equation.




Global Instance Z_has_total_time
  := { generate_from_to_T from to := List.map Z.of_nat (seq (Z.to_nat from) (S (Z.to_nat (to - from)))) }.


Global Instance nat_has_count_alloc : has_count nat
  := { generate_from_to_T from to := seq from (S (to - from)) }.

Global Instance N_has_generate : has_generate N
  := { generate_from_to_T from to := List.map N.of_nat (seq (N.to_nat from) (S (N.to_nat (to - from)))) }.

Global Instance Z_has_generate : has_generate Z
  := { generate_from_to_T from to := List.map Z.of_nat (seq (Z.to_nat from) (S (Z.to_nat (to - from)))) }.



Class has_generate T := { generate_from_to_T : T -> T -> list T }.

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

(*


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

Definition polynomial := list (Q * Z) (* coef, exp *).

Definition integrate_poly (p : polynomial) : polynomial * Q (* logarithmic factor *)
  := (List.flat_map (fun '(coeff, exp) => if negb (exp =? -1)%Z
                                          then [(coeff / (exp + 1)%Z, (exp + 1)%Z)]
                                          else [])
                    p,
      List.fold_right
        (fun x y => x + y)%Q
        0%Q
        (List.map (fun '(coeff, exp) => if (exp =? -1)%Z then coeff else 0%Q) p)).
Definition diff_poly (p : polynomial) : polynomial
  := List.map (fun '(coeff, exp) => (coeff * (exp:Z), (exp - 1)%Z)) p.

Definition eval_poly (p : polynomial) (x : Q) : Q
  := List.fold_right (fun x y => x + y)%Q 0%Q
                     (List.map (fun '(coeff, exp) => coeff * Qpower x exp) p).

Inductive known_poly :=
| constant (c : Q)
| linear (m b : Q)
| quadratic (a b c : Q)
| cubic (a b c d : Q)
| quartic (a b c d e : Q)
| quintic (a b c d e f : Q)
.

Inductive known_equation :=
| poly (p : known_poly)
| logarithmic (a b : Q) (* a ln(b x) *)
| exponential (a b : Q) (* a exp(b x) *)
.

Coercion poly : known_poly >-> known_equation.

Definition eval_known_poly (p : known_poly) : polynomial
  := match p with
     | constant c => [(c, 0)]
     | linear m b => [(m, 1); (b, 0)]
     | quadratic a b c => [(a, 2); (b, 1); (c, 0)]
     | cubic a b c d => [(a, 3); (b, 2); (c, 1); (d, 0)]
     | quartic a b c d e => [(a, 4); (b, 3); (c, 2); (d, 1); (e, 0)]
     | quintic a b c d e f => [(a, 5); (b, 4); (c, 3); (d, 2); (e, 1); (f, 0)]
     end%Z.

Definition reify_known_poly_helper (low_to_high_coef : list Q) : known_poly * polynomial
  := let above_hi_deg := 6%nat in
     let '(f, e, d, c, b, a, rest) :=
         let '(f, e, d, c, b, a, rest) := (0, 0, 0, 0, 0, 0, []) in
         match low_to_high_coef with
         | [] => (f, e, d, c, b, a, rest)
         | [a] => (f, e, d, c, b, a, rest)
         | [a; b] => (f, e, d, c, b, a, rest)
         | [a; b; c] => (f, e, d, c, b, a, rest)
         | [a; b; c; d] => (f, e, d, c, b, a, rest)
         | [a; b; c; d; e] => (f, e, d, c, b, a, rest)
         | [a; b; c; d; e; f] => (f, e, d, c, b, a, rest)
         | a::b::c::d::e::f::rest => (f, e, d, c, b, a, rest)
         end in
     let rest := List.map (fun '(coeff, exp) => (coeff, Z.of_nat exp))
                          (List.combine rest (seq above_hi_deg (List.length rest))) in
     (match Qeq_bool f 0, Qeq_bool e 0, Qeq_bool d 0, Qeq_bool c 0, Qeq_bool b 0, Qeq_bool a 0 with
      | true, true, true, true, true, _
        => constant a
      | true, true, true, true, _, _
        => linear b a
      | true, true, true, _, _, _
        => quadratic c b a
      | true, true, _, _, _, _
        => cubic d c b a
      | true, _, _, _, _, _
        => quartic e d c b a
      | _, _, _, _, _, _
        => quintic f e d c b a
      end,
      rest).

Definition reify_known_poly (p : polynomial) : known_poly * polynomial
  := let max_deg := Z.to_nat (List.fold_right Z.max 0%Z (List.map (@snd _ _) p)) in
     let low_to_high_coef := List.map (fun n:nat => List.fold_right (fun x y => x + y)%Q 0%Q (List.map (@fst _ _) (List.filter (fun '(coeff, exp) => (exp =? n)%Z) p))) (seq 0 (S max_deg)) in
     let low := List.filter (fun '(coeff, exp) => (exp <? 0)%Z) p in
     let '(p, rest) := reify_known_poly_helper low_to_high_coef in
     (p, low ++ rest).

Definition e_Q : Q := 2.7182818284590452353602874713526624977572470936999595749669676277.
Definition log2_e_Q : Q := 1.4426950408889634073599246810018921374266459541529859341354494069.

Fixpoint fact (n : nat) : N
  := match n with
     | O => 1
     | S n' => n * fact n'
     end%N.

Definition fact0 : N := Eval compute in fact 0.
Definition fact1 : N := Eval compute in fact 1.
Definition fact2 : N := Eval compute in fact 2.
Definition fact3 : N := Eval compute in fact 3.
Definition fact4 : N := Eval compute in fact 4.
Definition fact5 : N := Eval compute in fact 5.
Definition fact6 : N := Eval compute in fact 6.
Definition fact7 : N := Eval compute in fact 7.

Fixpoint taylor_series_exp (deg : nat) : polynomial
  := match deg with
     | O => [(1, 0%Z)]
     | S deg'
       => ((1/fact deg), Z.of_nat deg) :: taylor_series_exp deg'
     end.

Definition taylor_series_exp_for_exp := Eval compute in taylor_series_exp 5.

Fixpoint taylor_series_ln1px (deg : nat) : polynomial
  := match deg with
     | O => []
     | S deg'
       => (((-1)^(deg'))%Z / deg, Z.of_nat deg) :: taylor_series_ln1px deg'
     end.

Definition taylor_series_ln1px_for_ln := Eval compute in taylor_series_ln1px 5.

Definition prod_from_to (lower upper : Z) (f : Z -> Q) : Q
  := List.fold_right (fun x y => x * y)%Q
                     1%Q
                     (List.map (fun x:nat => f (lower + x)%Z) (seq 0 (1 + Z.to_nat (upper - lower)))).

Local Notation "'Π_{' x = lower '}^{' upper } f"
  := (prod_from_to lower upper (fun x => f))
       (x ident, at level 35).

Fixpoint taylor_series_1pxpow (exp : Q) (deg : nat) : polynomial
  := match deg with
     | O => [(1, 0%Z)]
     | S deg'
       => let '(s, t) := (Qnum exp, Qden exp) in
          let n := deg in
          ((Π_{ k = 0 }^{ n - 1 } (s - k * t)) / (fact n * t^n)%Z,
           Z.of_nat n)
            :: taylor_series_1pxpow exp deg'
     end.

Local Arguments Pos.to_nat !_ / .

Definition taylor_series_1pxpow_for_pow (exp : Q)
  := Eval cbn [taylor_series_1pxpow fact N.mul N.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z.of_nat] in taylor_series_1pxpow exp 5.

Definition Qlog2_up (x : Q) : Z
  := (Z.log2_up (Qnum x) - Z.log2 (Qden x))%Z.
Definition Qlog2 (x : Q) : Z
  := (Z.log2 (Qnum x) - Z.log2_up (Qden x))%Z.

Definition Qln (x : Q) : Q
  := (* let x = 2^k * (1+q), so that either k:=log2_up(x) or k:=log2(x) and q:=x/2^k-1; then ln(x) = k/log2(e) + ln(1+q) *)
    let k := if Qle_bool ((2^Qlog2_up x)%Z - x) (x - (2^Qlog2 x)%Z)
             then Qlog2_up x
             else Qlog2 x in
    let q := x / (2^k)%Z - 1 in
    k / log2_e_Q + if Qeq_bool q 0 then 0 else eval_poly taylor_series_ln1px_for_ln q.

Definition Qexp (x : Q) : Q
  := let (int_part, rest)
         := if Qle_bool (x - Qfloor x) (Qceiling x - x)
            then (Qfloor x, x - Qfloor x)
            else (Qceiling x, x - Qceiling x) in
     Qpower e_Q int_part
     * if Qeq_bool rest 0 then 1 else eval_poly taylor_series_exp_for_exp rest.

Definition Qpow' (x : Q) (k : Q)
  := let (int_part, rest)
         := if Qle_bool (k - Qfloor k) (Qceiling k - k)
            then (Qfloor k, k - Qfloor k)
            else (Qceiling k, k - Qceiling k) in
     Qred (Qpower x int_part)
     * (* x^k = exp(ln(x^k)) = exp(k ln x) *)
     Qexp (rest * Qln x).

Definition Qroot_of_Qroot_up_down (e : positive) (Qroot_up : Q -> Q) (Qroot_down : Q -> Q)
           (x : Q) : Q
  := if Qle_bool 0 x
     then let vu := Qroot_up x in
          let vd := Qroot_down x in
          let v := if Qle_bool (x - Qpower vd e) (Qpower vu e - x) then vd else vu in
          (* x^(1/e) = v(1 + (x - v^e)/v^e)^(1/e) *)
          v * eval_poly (taylor_series_1pxpow_for_pow (1#e)) (x / Qpower v e - 1)
     else Qpow' x (1#e).

Definition Qsqrt (x : Q)
  := Qroot_of_Qroot_up_down
       2
       (fun x => (Z.sqrt_up (Qnum x)) # (Pos.sqrt (Qden x)))
       (fun x => (Z.sqrt (Qnum x)) # (Z.to_pos (Z.sqrt_up (Qden x))))
       x.

Definition eval_equ (e : known_equation) (x : Q) : Q
  := match e with
     | poly p => eval_poly (eval_known_poly p) x
     | logarithmic a b => a * Qln (b * x)
     | exponential a b => a * Qexp (b * x)
     end.

Definition inverse_equ (e : known_equation) (y : Q) : list Q
  := match e with
     | constant c => []
     | linear m b (* y = m x + b *)
       => [(y - b) / m]
     | quadratic a b c (* y = a x^2 + b x + c *)
       => let c := c - y in
          let descr := b*b - 4 * a * c in
          if Qle_bool 0 descr
          then List.map (fun sgn => (-b + sgn * Qsqrt descr) / (2 * a))
                        [-1; 1]
          else []
     | cubic a b c d => []
     | quartic a b c d e => []
     | quintic a b c d e f => []
     | logarithmic a b => []
     | exponential a b => []
     end.


Fixpoint binary_alloc_fueled
         (make_alloc : T -> nat (* count *) -> list T' * list T)
         (size : T -> Q)
         (allocation : Q)
         (max : T)
         (min : T)
         (ave : T -> T -> T)
         (fuel : nat)
  : list T' * Q (* allocation used *)
  := match fuel with
     | O => nil
     | S fuel
       => if (Qeq_bool (size min) (size (ave min max)) || Qeq_bool (size max) (size (ave min max)))
          then (* we've reached a very small interval *)
            if (Qeq_bool (size
       if (Qle_bool (size min + size max + size (ave min max)) allocation
              && Qle_bool (size (ave min max) + size max) (allocation / 2))
               (* there's plenty of allocation *)
          then
            let '(retr, allocation_usedr) := binary_alloc_fueled make_alloc size (allocation / 2) max (ave min max) ave fuel in
            let '(retl, allocation_usedl) := binary_alloc_fueled make_alloc size (allocation - allocation_usedr) (ave min max) ave fuel in
            (retl ++ retr, allocation_usedl + allocation_usedr)
          else
            if Qle_bool (size max) allocation
            then let '(ret, ret_res) := make_alloc max 1 in
                 (ret, fold_right (fun x y => x + y) 0%Q (List.map size ret_res))
            else if Qle_bool (size (ave min max))


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
x  := binary_alloc size allocation (sort_by size ls).

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
*)
