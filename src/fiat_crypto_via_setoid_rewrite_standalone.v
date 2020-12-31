Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.QArith.QArith_base Coq.QArith.Qreduction Coq.QArith.Qround.
Import List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Hint Rewrite <- pred_Sn : mydb.
Lemma Z_of_nat_O : Z.of_nat 0 = 0. Proof. reflexivity. Qed.
Hint Rewrite Z_of_nat_O : mydb.
Lemma Z_of_nat_S : forall x, Z.of_nat (S x) = Z.pos (Pos.of_succ_nat x). Proof. reflexivity. Qed.
Hint Rewrite Z_of_nat_S : mydb.
Lemma fst_pair {A B} (a : A) (b : B) : fst (a, b) = a.
Proof. reflexivity. Qed.
Lemma snd_pair {A B} (a : A) (b : B) : snd (a, b) = b.
Proof. reflexivity. Qed.
Hint Rewrite @fst_pair @snd_pair : mydb.
Lemma Z_mul_pos_pos x y : Z.pos x * Z.pos y = Z.pos (x * y). Proof. reflexivity. Qed.
Hint Rewrite Z_mul_pos_pos : mydb.
Hint Rewrite Z.mul_0_l Z.mul_0_r Z.opp_0 : mydb.
Lemma Z_div_0_l_pos x : 0 / Z.pos x = 0. Proof. reflexivity. Qed.
Hint Rewrite Z_div_0_l_pos : mydb.
Lemma Z_opp_pos x : Z.opp (Z.pos x) = Z.neg x. Proof. reflexivity. Qed.
Hint Rewrite Z_opp_pos : mydb.
Lemma Z_opp_neg x : Z.opp (Z.neg x) = Z.pos x. Proof. reflexivity. Qed.
Hint Rewrite Z_opp_neg : mydb.
Definition Z_div_unfolded := Eval cbv in Z.div.
Lemma unfold_Z_div_pos_pos x y : Z.div (Z.pos x) (Z.pos y) = Z_div_unfolded (Z.pos x) (Z.pos y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_pos_neg x y : Z.div (Z.pos x) (Z.neg y) = Z_div_unfolded (Z.pos x) (Z.neg y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_neg_pos x y : Z.div (Z.neg x) (Z.pos y) = Z_div_unfolded (Z.neg x) (Z.pos y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_neg_neg x y : Z.div (Z.neg x) (Z.neg y) = Z_div_unfolded (Z.neg x) (Z.neg y).
Proof. reflexivity. Qed.
Hint Rewrite unfold_Z_div_neg_neg unfold_Z_div_neg_pos unfold_Z_div_pos_neg unfold_Z_div_pos_pos : mydb.
Hint Rewrite Z.pow_0_r : mydb.
Definition Z_pow_unfolded := Eval cbv in Z.pow.
Lemma Z_pow_pos_pos x y : Z.pow (Z.pos x) (Z.pos y) = Z_pow_unfolded (Z.pos x) (Z.pos y). Proof. reflexivity. Qed.
Hint Rewrite Z_pow_pos_pos : mydb.
Lemma app_cons A (x : A) xs ys : (x :: xs) ++ ys = x :: (xs ++ ys).
Proof. reflexivity. Qed.
Hint Rewrite app_cons : mydb.
Lemma app_nil A xs : @nil A ++ xs = xs.
Proof. reflexivity. Qed.
Hint Rewrite app_nil : mydb.
Lemma partition_cons A f x xs : @partition A f (x :: xs) = prod_rect (fun _ => _) (fun g d => if f x then (x :: g, d) else (g, x :: d)) (partition f xs).
Proof. reflexivity. Qed.
Hint Rewrite partition_cons : mydb.
Lemma partition_nil A f : @partition A f nil = (nil, nil). Proof. reflexivity. Qed.
Hint Rewrite partition_nil : mydb.
Lemma prod_rect_pair A B P f x y : @prod_rect A B P f (x, y) = f x y. Proof. reflexivity. Qed.
Hint Rewrite prod_rect_pair : mydb.
Definition Z_modulo_unfolded := Eval cbv in Z.modulo.
Lemma Z_modulo_pos_pos x y : Z.modulo (Z.pos x) (Z.pos y) = Z_modulo_unfolded (Z.pos x) (Z.pos y).
Proof. reflexivity. Qed.
Hint Rewrite Z_modulo_pos_pos : mydb.
Hint Rewrite Z.eqb_refl Nat.eqb_refl : mydb.
Definition Pos_eqb_unfolded := Eval cbv in Pos.eqb.
Lemma Z_eqb_pos_pos x y : Z.eqb (Z.pos x) (Z.pos y) = Pos_eqb_unfolded x y. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_pos : mydb.
Lemma Z_eqb_neg_neg x y : Z.eqb (Z.neg x) (Z.neg y) = Pos_eqb_unfolded x y. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_neg : mydb.
Lemma Z_eqb_pos_0 x : Z.eqb (Z.pos x) 0 = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_0 : mydb.
Lemma Z_eqb_0_pos x : Z.eqb 0 (Z.pos x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_0_pos : mydb.
Lemma Z_eqb_pos_neg x y : Z.eqb (Z.pos x) (Z.neg y) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_neg : mydb.
Lemma Z_eqb_neg_pos y x : Z.eqb (Z.neg y) (Z.pos x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_pos : mydb.
Lemma Z_eqb_neg_0 x : Z.eqb (Z.neg x) 0 = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_0 : mydb.
Lemma Z_eqb_0_neg x : Z.eqb 0 (Z.neg x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_0_neg : mydb.
Lemma length_nil A : List.length (@nil A) = 0%nat. Proof. reflexivity. Qed.
Lemma map_cons A B (f : A -> B) (x : A) (l : list A) : List.map f (x :: l) = f x :: List.map f l.
Proof. reflexivity. Qed.
Lemma map_nil A B (f : A -> B) : List.map f [] = [].
Proof. reflexivity. Qed.
Lemma length_cons {T} (x : T) (xs : list T) : Datatypes.length (x :: xs) = S (Datatypes.length xs).
Proof. reflexivity. Qed.
Hint Rewrite map_cons map_nil @length_cons length_nil : mydb.
Lemma flat_map_cons {A B} (f : A -> list B) (x : A) (xs : list A) : flat_map f (x :: xs) = (f x ++ flat_map f xs)%list.
Proof. reflexivity. Qed.
Lemma flat_map_nil {A B} (f : A -> list B) : flat_map f [] = [].
Proof. reflexivity. Qed.
Hint Rewrite @flat_map_cons @flat_map_nil : mydb.
Lemma nat_eqb_S_O x : Nat.eqb (S x) O = false. Proof. reflexivity. Qed.
Hint Rewrite nat_eqb_S_O : mydb.
Lemma nat_eqb_O_S x : Nat.eqb O (S x) = false. Proof. reflexivity. Qed.
Hint Rewrite nat_eqb_O_S : mydb.
Lemma fold_right_cons {A B} (f : B -> A -> A) (a : A) (b : B) (bs : list B) : fold_right f a (b :: bs) = f b (fold_right f a bs).
Proof. reflexivity. Qed.
Lemma fold_right_nil {A B : Type} (f : B -> A -> A) (a : A) : fold_right f a [] = a.
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_cons @fold_right_nil : mydb.
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Notation "'dlet' x .. y := v 'in' f" := (Let_In v (fun x => .. (fun y => f) .. )).
Strategy 100 [Let_In].

Global Instance Proper_Let_In_nd_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof. lazy; intros; subst; auto; congruence. Qed.

Global Instance Proper_Let_In_nd_changevalue {A B} (RA:relation A) {RB:relation B}
  : Proper (RA ==> (RA ==> RB) ==> RB) (Let_In (P:=fun _=>B)).
Proof. cbv; intuition. Qed.

Lemma Proper_Let_In_nd_changebody_eq {A P R} {Reflexive_R:@Reflexive P R} {x}
  : Proper ((fun f g => forall a, x = a -> R (f a) (g a)) ==> R) (@Let_In A (fun _ => P) x).
Proof. lazy; intros; subst; auto; congruence. Qed.

Global Instance Proper_Let_In_nd_changevalue_forall {A B} {RB:relation B}
  : Proper (eq ==> (forall_relation (fun _ => RB)) ==> RB) (Let_In (P:=fun _:A=>B)).
Proof. cbv; intuition (subst; eauto). Qed.

(* Strangely needed in some cases where we have [(fun _ => foo) ...] messing up dependency calculation *)
Hint Extern 1 (Proper _ (@Let_In _ _)) => progress cbv beta : typeclass_instances.

Definition app_Let_In_nd {A B T} (f:B->T) (e:A) (C:A->B)
  : f (Let_In e C) = Let_In e (fun v => f (C v)) := eq_refl.

Definition Let_app_In_nd {A B T} (f:A->B) (e:A) (C:B->T)
  : Let_In (f e) C = Let_In e (fun v => C (f v)) := eq_refl.

Lemma unfold_Let_In {A B} v f : @Let_In A B v f = f v.
Proof. reflexivity. Qed.
Lemma dlet_pair A B T x y f : Let_In (@pair A B x y) f = (dlet x' := x in dlet y' := y in f (x', y')) :> T.
Proof. reflexivity. Qed.
Hint Rewrite dlet_pair : mydb letdb.
Lemma lift_dlet A B C x (f : A -> B) (g : B -> C) : g (Let_In x f) = Let_In x (fun x' => g (f x')). Proof. reflexivity. Qed.
Definition lift_dlet_list A B C := @lift_dlet A B (list C).
Definition lift_dlet_prod A B C1 C2 := @lift_dlet A B (C1 * C2).
Definition lift_dlet_nat A B := @lift_dlet A B nat.
Definition lift_dlet_Z A B := @lift_dlet A B Z.
Hint Rewrite lift_dlet_list lift_dlet_prod lift_dlet_nat lift_dlet_Z : mydb letdb.
Lemma lift_dlet1 A B C D x y (f : A -> B) (g : B -> C -> D) : g (Let_In x f) y = Let_In x (fun x' => g (f x') y). Proof. reflexivity. Qed.
Definition lift_dlet1_list A B C D := @lift_dlet1 A B C (list D).
Definition lift_dlet1_prod A B C D1 D2 := @lift_dlet1 A B C (D1 * D2).
Definition lift_dlet1_nat A B C := @lift_dlet1 A B C nat.
Definition lift_dlet1_Z A B C := @lift_dlet1 A B C Z.
Hint Rewrite lift_dlet1_list lift_dlet1_prod lift_dlet1_nat lift_dlet1_Z : mydb letdb.
Lemma inline_dlet_S B x (f : nat -> B) : Let_In (S x) f = f (S x). Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_S : mydb letdb.
Lemma inline_dlet_O B (f : nat -> B) : Let_In O f = f O. Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_O : mydb letdb.
Lemma rev_nil A : rev (@nil A) = nil. Proof. reflexivity. Qed.
Lemma rev_cons {A} x ls : @rev A (x :: ls) = rev ls ++ [x]. Proof. reflexivity. Qed.
Hint Rewrite @rev_cons @rev_nil : mydb.
Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
        match n with
        | O => match xs with
                                 | nil => nil
                                 | x'::xs' => f x'::xs'
                                 end
        | S n' =>  match xs with
                                 | nil => nil
                                 | x'::xs' => x'::update_nth n' f xs'
                                 end
  end.
Lemma update_nth_nil : forall {T} n f, update_nth n f (@nil T) = @nil T.
Proof. destruct n; reflexivity. Qed.
Lemma update_nth_cons : forall {T} f (u0 : T) us, update_nth 0 f (u0 :: us) = (f u0) :: us.
Proof. reflexivity. Qed.
Hint Rewrite @update_nth_nil @update_nth_cons : mydb.
Lemma update_nth_S_cons T n f x xs : @update_nth T (S n) f (x :: xs) = x :: update_nth n f xs.
Proof. reflexivity. Qed.
Hint Rewrite update_nth_S_cons : mydb.
Lemma combine_cons : forall {A B} a b (xs:list A) (ys:list B),
  combine (a :: xs) (b :: ys) = (a,b) :: combine xs ys.
Proof. reflexivity. Qed.
Lemma combine_nil_r : forall {A B} (xs:list A),
  combine xs (@nil B) = nil.
Proof. destruct xs; reflexivity. Qed.
Hint Rewrite @combine_cons @combine_nil_r : mydb.
Lemma app_dlet A B x (f : A -> list B) ys : (Let_In x f) ++ ys = Let_In x (fun x' => f x' ++ ys).
Proof. reflexivity. Qed.
Hint Rewrite app_dlet : mydb letdb.
Definition expand_list_helper {A} (default : A) (ls : list A) (n : nat) (idx : nat) : list A
  := nat_rect
       (fun _ => nat -> list A)
       (fun _ => nil)
       (fun n' rec_call idx
        => cons (List.nth_default default ls idx) (rec_call (S idx)))
       n
       idx.
Definition expand_list {A} (default : A) (ls : list A) (n : nat) : list A
  := expand_list_helper default ls n 0.
Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.


Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).
  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).
  Definition repeat_reduce (n : nat) (s:Z) (c:list _) (p:list _) : list (Z * Z)
    := nat_rect
         _
         (fun p => p)
         (fun n' repeat_reduce_n' p
          => let lo_hi := split s p in
             if (length (snd lo_hi) =? 0)%nat
             then p
             else let p := fst lo_hi ++ mul c (snd lo_hi) in
                  repeat_reduce_n' p)
         n
         p.
  Section Carries.
    Definition carryterm (w fw:Z) (t:Z * Z) :=
      if (Z.eqb (fst t) w)
      then dlet t2 := snd t in
           dlet d2 := t2 / fw in
           dlet m2 := t2 mod fw in
           [(w * fw, d2);(w,m2)]
      else [t].
    Definition carry (w fw:Z) (p:list (Z * Z)):=
      flat_map (carryterm w fw) p.
  End Carries.
End Associational.
Module Positional.
  Section Positional.
  Context (weight : nat -> Z).

  Definition to_associational (n:nat) (xs:list Z) : list (Z*Z)
    := combine (map weight (List.seq 0 n)) xs.
  Definition zeros n : list Z := repeat 0 n.
  Definition add_to_nth i x (ls : list Z) : list Z
    := update_nth i (fun y => x + y) ls.
  Definition place (t:Z*Z) (i:nat) : nat * Z :=
    nat_rect
      (fun _ => unit -> (nat * Z)%type)
      (fun _ => (O, fst t * snd t))
      (fun i' place_i' _
       => let i := S i' in
          if (fst t mod weight i =? 0)
          then (i, let c := fst t / weight i in c * snd t)
          else place_i' tt)
      i
      tt.
  Definition from_associational n (p:list (Z*Z)) :=
    List.fold_right (fun t ls =>
      dlet p := place t (pred n) in
      add_to_nth (fst p) (snd p) ls ) (zeros n) p.
  Section mulmod.
    Context (s:Z)
            (c:list (Z*Z)).
    Definition mulmod (n:nat) (a b:list Z) : list Z
      := let a_a := to_associational n a in
         let b_a := to_associational n b in
         let ab_a := Associational.mul a_a b_a in
         let abm_a := Associational.repeat_reduce n s c ab_a in
         from_associational n abm_a.
  End mulmod.

  Section Carries.
    Definition carry n m (index:nat) (p:list Z) : list Z :=
      from_associational
        m (@Associational.carry (weight index)
                                (weight (S index) / weight index)
                                (to_associational n p)).

    Definition carry_reduce n (s:Z) (c:list (Z * Z))
               (index:nat) (p : list Z) :=
      from_associational
        n (Associational.reduce
             s c (to_associational (S n) (@carry n (S n) index p))).
    Definition chained_carries n s c p (idxs : list nat) :=
      fold_right (fun a b => carry_reduce n s c a b) p (rev idxs).
  End Carries.
  End Positional.
End Positional.

Lemma split_cons s p ps : Associational.split s (p :: ps) = prod_rect (fun _ => _) (fun hi lo => (lo, List.map (fun t : Z * Z => (fst t / s, snd t)) hi)) (partition (fun t : Z * Z => fst t mod s =? 0) (p :: ps)).
Proof.
  cbv [Associational.split prod_rect]; edestruct partition; reflexivity.
Qed.
Hint Rewrite split_cons : mydb.
Lemma mul_cons_cons p ps q qs : Associational.mul (p :: ps) (q :: qs) = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) (q :: qs)) (p :: ps).
Proof. reflexivity. Qed.
Hint Rewrite mul_cons_cons : mydb.
Lemma mul_cons_nil p ps : Associational.mul (p :: ps) nil = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) nil) (p :: ps).
Proof. reflexivity. Qed.
Hint Rewrite mul_cons_nil : mydb.
Lemma mul_nil_cons q qs : Associational.mul nil (q :: qs) = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) (q :: qs)) nil.
Proof. reflexivity. Qed.
Hint Rewrite mul_nil_cons : mydb.
Lemma mul_nil_nil : Associational.mul nil nil = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) nil) nil.
Proof. reflexivity. Qed.
Hint Rewrite mul_nil_nil : mydb.
Lemma unfold_reduce s c p : Associational.reduce s c p = prod_rect (fun _ => _) (fun lo hi => lo ++ Associational.mul c hi) (Associational.split s p).
Proof. cbv [Associational.reduce]; edestruct Associational.split; reflexivity. Qed.
Hint Rewrite unfold_reduce : mydb.
Lemma nat_rect_O P fO fS : nat_rect P fO fS 0 = fO.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_O : mydb.
Lemma nat_rect_O_arr P Q fO fS x : nat_rect (fun n => P n -> Q n) fO fS 0 x = fO x.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_O_arr : mydb.
Lemma nat_rect_S P fO fS n : nat_rect P fO fS (S n) = fS n (nat_rect P fO fS n).
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_S : mydb.
Lemma nat_rect_S_arr P Q fO fS n x : nat_rect (fun n => P n -> Q n) fO fS (S n) x = fS n (nat_rect _ fO fS n) x.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_S_arr : mydb.
Lemma pointwise_map {A B} : Proper ((pointwise_relation _ eq) ==> eq ==> eq) (@List.map A B).
Proof.
  repeat intro; cbv [pointwise_relation] in *; subst.
  match goal with [H:list _ |- _ ] => induction H as [|? IH IHIH] end; [reflexivity|].
  simpl. rewrite IHIH. congruence.
Qed.
Global Instance fold_right_Proper {A B} : Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_right A B) | 1.
Proof.
  cbv [pointwise_relation]; intros f g Hfg x y ? ls ls' ?; subst y ls'; revert x.
  induction ls as [|l ls IHls]; cbn [fold_right]; intro; rewrite ?IHls, ?Hfg; reflexivity.
Qed.


Module ModOps.
  Section mod_ops.
    Import Positional.
    Local Coercion Z.of_nat : nat >-> Z.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (idxs : list nat).
  Definition weight (i : nat)
    := 2^(-(-(limbwidth_num * i) / limbwidth_den)).
  Definition carry_mulmod (f g : list Z) : list Z
    := chained_carries weight n s c (mulmod weight s c n f g) idxs.
  End mod_ops.
End ModOps.

Ltac make_eq_rel T :=
  lazymatch T with
  | (?A -> ?B)
    => let RB := make_eq_rel B in
      constr:(@respectful A B (@eq A) RB)
  | (forall a : ?A, ?B)
    => let B' := fresh in
      constr:(@forall_relation A (fun a : A => B) (fun a : A => match B with B' => ltac:(let B'' := (eval cbv delta [B'] in B') in
                                                                                  let RB := make_eq_rel B in
                                                                                  exact RB) end))
  | _ => constr:(@eq T)
  end.
Ltac solve_Proper_eq :=
  match goal with
  | [ |- @Proper ?A ?R ?f ]
    => let R' := make_eq_rel A in
      unify R R';
      apply (@reflexive_proper A R')
  end.
Hint Extern 0 (Proper _ _) => solve_Proper_eq : typeclass_instances.

Declare Reduction mycbv := cbv [Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z_div_unfolded Z_pow_unfolded Z_modulo_unfolded Pos_eqb_unfolded].
Ltac mycbv := cbv [Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z_div_unfolded Z_pow_unfolded Z_modulo_unfolded Pos_eqb_unfolded].

Declare Reduction morecbv := cbv [Associational.repeat_reduce Positional.from_associational Positional.zeros repeat Positional.place Positional.chained_carries Positional.add_to_nth Positional.carry_reduce Positional.carry Positional.to_associational seq Associational.carry Associational.carryterm].
Ltac morecbv := cbv [Associational.repeat_reduce Positional.from_associational Positional.zeros repeat Positional.place Positional.chained_carries Positional.add_to_nth Positional.carry_reduce Positional.carry Positional.to_associational seq Associational.carry Associational.carryterm].

Opaque Let_In.
Hint Constants Opaque : rewrite.

Global Instance flat_map_Proper A B : Proper (pointwise_relation _ eq ==> eq ==> eq) (@flat_map A B).
Proof. Admitted.

Global Instance map_Proper_eq {A B} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.map A B) | 1.
Proof. repeat intro; subst; apply pointwise_map; repeat intro; eauto. Qed.
Global Instance flat_map_Proper_eq {A B} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.flat_map A B) | 1.
Proof. repeat intro; subst; apply flat_map_Proper; repeat intro; eauto. Qed.
Global Instance partition_Proper {A} : Proper (pointwise_relation _ eq ==> eq ==> eq) (@List.partition A).
Proof.
  cbv [pointwise_relation]; intros f g Hfg ls ls' ?; subst ls'.
  induction ls as [|l ls IHls]; cbn [partition]; rewrite ?IHls, ?Hfg; reflexivity.
Qed.
Global Instance partition_Proper_eq {A} : Proper ((eq ==> eq) ==> eq ==> eq) (@List.partition A) | 1.
Proof. repeat intro; subst; apply partition_Proper; repeat intro; eauto. Qed.
Global Instance fold_right_Proper_eq {A B} : Proper ((eq ==> eq ==> eq) ==> eq ==> eq ==> eq) (@fold_right A B) | 1.
Proof. cbv [respectful]; repeat intro; subst; apply fold_right_Proper; repeat intro; eauto. Qed.
Global Instance: forall {A}, Proper (eq ==> eq ==> Basics.flip Basics.impl) (@eq A) := _.
Global Instance: forall {A}, Proper (eq ==> pointwise_relation _ (Basics.flip eq) ==> eq ==> eq) (@update_nth A).
Proof. Admitted.
Global Instance: forall {A}, Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq) (@update_nth A).
Proof. Admitted.
Global Instance: forall A B, Proper (eq ==> eq ==> eq) (@pair A B) := _.
Global Instance: forall A B P, Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq) (@prod_rect A B (fun _ => P)).
Proof. intros ? ? ? f g Hfg [? ?] ? ?; subst; apply Hfg. Qed.
Global Instance: Transitive (Basics.flip Basics.impl) := _.
Existing Instance pointwise_map.
Existing Instance fold_right_Proper.
Global Instance: forall A B, Proper (forall_relation (fun _ => pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_right A B).
Proof. intros ? ? f g Hfg. apply fold_right_Proper, Hfg. Qed.
Global Instance: forall A B x, (Proper (pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => B) x)) := _.
Global Instance:
  forall A B,
    Proper
      ((eq ==> eq)
         ==> (eq ==> (eq ==> eq) ==> eq ==> eq)
         ==> eq
         ==> eq
         ==> eq)
      (nat_rect (fun _ => A -> B)).
Proof.
  cbv -[nat_rect]; intros ???????? n n' ? y y' ?; subst n' y'; subst; revert y.
  induction n; cbn; intros; eauto.
  match goal with H : _ |- _ => apply H; intuition (subst; eauto) end.
Qed.
Global Instance: Proper (eq ==> eq ==> eq) Z.mul := _.
Global Instance: forall {A}, Proper (eq ==> eq ==> eq) (@cons A) := _.
Global Instance: forall {A}, Proper (eq ==> eq ==> eq) (@app A) := _.
Global Instance: forall {A B f}, Proper (@eq A ==> @eq B) f := _.
Global Instance: forall {A B C f}, Proper (@eq A ==> @eq B ==> @eq C) f := _.
Global Instance: forall {A B}, Proper (eq ==> pointwise_relation A (@eq B) ==> eq) Let_In := _.
Global Instance: forall {A B}, Proper (eq ==> forall_relation (fun _ : A => @eq B) ==> eq) Let_In := _.
Global Instance: forall {A a}, ProperProxy (@eq A) a := _.
Global Instance: forall {A B f}, ProperProxy (pointwise_relation A (@eq B)) f := _.
Global Instance: forall {A B f}, ProperProxy (forall_relation (fun _ : A => @eq B)) f.
Proof. cbv; reflexivity. Qed.

Module ViaSetoidRewrite.
  Ltac go_step :=
    time (match goal with |- ?G => idtac "Goal:" G end;
          first [ time setoid_rewrite lift_dlet
                | time setoid_rewrite lift_dlet1
                | match goal with
                  | [ |- context[Let_In _ _ ++ _] ] => setoid_rewrite app_dlet
                  | [ |- context[dlet x := (_, _) in _] ] => setoid_rewrite dlet_pair
                  | [ |- context[Let_In O] ] => setoid_rewrite inline_dlet_O
                  | [ |- context[Let_In (S ?x)] ] => setoid_rewrite inline_dlet_S
                  end
                | time progress mycbv
                | time progress rewrite ?Z_of_nat_O, ?Z_of_nat_S, ?Z_mul_pos_pos, ?Z.mul_0_l, ?Z.mul_0_r, ?Z.opp_0, ?Z_div_0_l_pos, ?Z_opp_pos, ?Z_opp_neg, ?unfold_Z_div_pos_pos, ?unfold_Z_div_pos_neg, ?unfold_Z_div_neg_pos,?unfold_Z_div_neg_neg, ?Z.pow_0_r, ?Z_pow_pos_pos, ?Z_modulo_pos_pos, ?Z_eqb_pos_pos, ?Z.eqb_refl, ?Nat.eqb_refl, ?Z_eqb_neg_neg, ?Z_eqb_pos_0, ?Z_eqb_0_pos, ?Z_eqb_pos_neg, ?Z_eqb_neg_pos, ?Z_eqb_neg_0, ?Z_eqb_0_neg, ?length_nil, <- ?pred_Sn, ?nat_eqb_S_O, ?nat_eqb_O_S
                | progress cbn [nat_rect]
                | match goal with
                  | [ |- context[prod_rect _ (_, _)] ] => setoid_rewrite prod_rect_pair
                  | [ |- context[List.length (_ :: _)] ] => setoid_rewrite @length_cons
                  | [ |- context[fst (_, _)] ] => setoid_rewrite @fst_pair
                  | [ |- context[snd (_, _)] ] => setoid_rewrite @snd_pair
                  | [ |- context[(_ :: _) ++ _] ] => setoid_rewrite app_cons
                  | [ |- context[nil ++ _] ] => setoid_rewrite app_nil
                  | [ |- context[rev (_ :: _)] ] => setoid_rewrite rev_cons
                  | [ |- context[rev nil] ] => setoid_rewrite rev_nil
                  | [ |- context[prod_rect _ _ (_, _)] ] => setoid_rewrite prod_rect_pair
                  | [ |- context[partition _ nil] ] => setoid_rewrite partition_nil
                  | [ |- context[fold_right _ _ nil] ] => setoid_rewrite @fold_right_nil
                  | [ |- context[update_nth _ _ nil] ] => setoid_rewrite @update_nth_nil
                  | [ |- context[update_nth O _ (_ :: _)] ] => setoid_rewrite @update_nth_cons
                  | [ |- context[update_nth (S _) _ (_ :: _)] ] => setoid_rewrite @update_nth_S_cons
                  | [ |- context[List.map _ nil] ] => setoid_rewrite map_nil
                  | [ |- context[List.combine _ nil] ] => setoid_rewrite @combine_nil_r
                  | [ |- context[flat_map _ nil] ] => setoid_rewrite @flat_map_nil
                  | [ |- context[partition _ (_ :: _)] ] => setoid_rewrite partition_cons
                  | [ |- context[fold_right _ _ (_ :: _)] ] => setoid_rewrite @fold_right_cons
                  | [ |- context[List.map _ (_ :: _)] ] => setoid_rewrite map_cons
                  | [ |- context[List.combine (_ :: _) (_ :: _)] ] => setoid_rewrite @combine_cons
                  | [ |- context[flat_map _ (_ :: _)] ] => setoid_rewrite @flat_map_cons
                  | [ |- context[Associational.split _ (_ :: _)] ] => setoid_rewrite split_cons
                  | [ |- context[Associational.reduce _ _ _] ] => setoid_rewrite unfold_reduce
                  | [ |- context[Associational.mul (_ :: _) (_ :: _)] ] => setoid_rewrite mul_cons_cons
                  | [ |- context[Associational.mul nil (_ :: _)] ] => setoid_rewrite mul_nil_cons
                  | [ |- context[Associational.mul (_ :: _) nil] ] => setoid_rewrite mul_cons_nil
                  | [ |- context[Associational.mul nil nil] ] => setoid_rewrite mul_nil_nil
                  | [ |- context[nat_rect _ _ _ O _] ] => idtac "0arr"; setoid_rewrite nat_rect_O_arr
                  | [ |- context[nat_rect _ _ _ (S _) _] ] => idtac "Sarr"; setoid_rewrite nat_rect_S_arr
                  | [ |- context[nat_rect _ _ _ (S _)] ] => idtac "S"; setoid_rewrite nat_rect_S
                  | [ |- context[nat_rect _ _ _ O] ] => idtac "0"; setoid_rewrite nat_rect_O
                  end
                | progress cbv [Associational.repeat_reduce]
                | progress cbv [Positional.from_associational]
                | progress cbv [Positional.zeros repeat]
                | progress cbv [Positional.place]
                | progress cbv [Positional.chained_carries]
                | progress cbv [Positional.add_to_nth]
                | progress cbv [Positional.carry_reduce Positional.carry Positional.to_associational seq Associational.carry Associational.carryterm] ]).
  Ltac go_count_max n max :=
    lazymatch max with
    | O => idtac "Not Finished:" n
    | _
      => let max := lazymatch max with
                    | S ?max => max
                    | _ => max
                    end in
         idtac "Cur:" n; tryif go_step then go_count_max (S n) max else idtac "Finished:" n
    end.
  Ltac go_count n := intros; go_count_max n tt.
  Ltac go := go_count O (*repeat go_step*).
End ViaSetoidRewrite.

Module ViaRewriteStrat.
  Ltac go :=
    intros;
    time (rewrite_strat (((topdown (hints mydb; eval mycbv));
                          eval cbv [Associational.repeat_reduce nat_rect Associational.split Associational.mul];
                          ((topdown (hints mydb; eval mycbv)));
                          eval cbv [Positional.from_associational Init.Nat.pred Positional.zeros repeat Positional.place nat_rect Positional.add_to_nth])));
    (* COQBUG(https://github.com/coq/coq/issues/10934) *)
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
    time (rewrite_strat eval cbv [Positional.chained_carries Positional.carry_reduce]);
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
    time (rewrite_strat eval cbv [Positional.carry Positional.to_associational Associational.carry seq Associational.carryterm Positional.from_associational]);
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
    time (rewrite_strat eval cbv [Init.Nat.pred Positional.zeros repeat Positional.place nat_rect]);
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
    time (rewrite_strat eval cbv [Positional.add_to_nth Associational.reduce]);(*.
        Set Printing Depth 1000000.
        Typeclasses eauto := debug.
        Time*)
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
    time (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv))))).
End ViaRewriteStrat.

Ltac print_goal _ :=
  match goal with |- ?G => idtac "Goal:" G end.

Class params :=
  { n : nat;
    s : Z;
    c : list (Z * Z);
    idxs : list nat;
    limbwidth := (inject_Z (Z.log2_up (s - Associational.eval c)) / inject_Z (Z.of_nat n))%Q;
    machine_wordsize : Z }.
(*
Require Import Crypto.Rewriter.PerfTesting.Core.
Import UnsaturatedSolinas Coq.Lists.List.ListNotations.
Set Printing Width 1000000.
Definition p' := Eval native_compute in of_string "2^61 - 1" 64.
Definition p : params
  := Eval vm_compute in Option.invert_Some (List.nth_error p' 0).
Print p.
 *)

Definition default_params_of_size (n : nat) : params
  := (* no recorded example, so fake one *)
    {| n := n; s := 2^(64 * Z.of_nat n + 1); c := [(1, 1)] ; idxs := seq 0 n ++ [0; 1]%nat; machine_wordsize := 64 |}.

Definition maybe_params_of_size (n : nat) : option params
  := match n with
     | 1%nat => (* 2^61-1, 1 limb *)
       Some {| n := 1; s := 2305843009213693952; c := [(1, 1)]; idxs := [0%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 2%nat => (* 2^107-1, 2 limbs *)
       Some {| n := 2; s := 162259276829213363391578010288128; c := [(1, 1)]; idxs := [0%nat; 1%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 3%nat => (* 2^127-1, 3 limbs *)
       Some {| n := 3; s := 170141183460469231731687303715884105728; c := [(1, 1)]; idxs := [0%nat; 1%nat; 2%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 4%nat => (* 2^190-11, 4 limbs *)
       Some {| n := 4; s := 1569275433846670190958947355801916604025588861116008628224; c := [(1, 11)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 5%nat => (* 2^255-19, 5 limbs *)
       Some {| n := 5; s := 57896044618658097711785492504343953926634992332820282019728792003956564819968; c := [(1, 19)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 6%nat => (* 2^321-9, 6 limbs *)
       Some {| n := 6; s := 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152; c := [(1, 9)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 7%nat => (* 2^389-21, 7 limbs *)
       Some {| n := 7; s := 1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112; c := [(1, 21)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 8%nat => (* 2^452-3, 8 limbs *)
       Some {| n := 8; s := 11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496; c := [(1, 3)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 9%nat => (* 2^521-1, 9 limbs *)
       Some {| n := 9; s := 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152; c := [(1, 1)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 10%nat => (* 2^255-19, 32-bit, 10 limbs *)
       Some {| n := 10; s := 57896044618658097711785492504343953926634992332820282019728792003956564819968; c := [(1, 19)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 0%nat; 1%nat]; machine_wordsize := 32 |}
     | 11%nat => (* 2^285-9, 32-bit, 11 limbs *)
       Some {| n := 11; s := 62165404551223330269422781018352605012557018849668464680057997111644937126566671941632; c := [(1, 9)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 0%nat; 1%nat]; machine_wordsize := 32 |}
     | 12%nat => (* 2^291-19, 32-bit, 12 limbs *)
       Some {| n := 12; s := 3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448; c := [(1, 19)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 0%nat; 1%nat]; machine_wordsize := 32 |}
     | 13%nat => (* 2^321-9, 32-bit, 13 limbs *)
       Some {| n := 13; s := 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152; c := [(1, 9)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 0%nat; 1%nat]; machine_wordsize := 32 |}
     | 15%nat => (* 2^369-25, 32-bit, 15 limbs *)
       Some {| n := 15; s := 1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712; c := [(1, 25)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 0%nat; 1%nat]; machine_wordsize := 32 |}
     | nlimbs => None
     end.

Ltac get_goal_of_size nlimbs :=
  let nlimbs := (eval cbv in nlimbs) in
  let p := (eval cbv in (maybe_params_of_size nlimbs)) in
  let __ := lazymatch p with None => idtac "Warning: faking parameters for size:" nlimbs | _ => idtac end in
  let p := lazymatch p with
           | Some ?p => p
           | None => (eval cbv in (default_params_of_size nlimbs))
           end in
  let v := constr:(let p' := p in
                   (fun f g : list Z => ModOps.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (expand_list 0 f n) (expand_list 0 g n))) in
  let v := (eval cbv -[ModOps.carry_mulmod expand_list] in v) in
  let g := constr:(forall f g, v f g = f) in
  let g := (eval cbv [expand_list ModOps.carry_mulmod expand_list_helper nat_rect ModOps.weight Positional.mulmod Positional.to_associational seq List.map List.combine Associational.mul flat_map] in g) in
  g.
Notation goal_of_size nlimbs := (match nlimbs%nat return _ with nlimbs' => ltac:(let g := get_goal_of_size nlimbs' in exact g) end) (only parsing).

Notation size_of_problem := 2%nat (only parsing).
Notation goal := (goal_of_size size_of_problem) (only parsing).

(* sanity check *)
Goal True.
  assert (goal_of_size 1).
  ViaRewriteStrat.go.
  lazymatch goal with
  | [ |- ?x = _ ]
    => lazymatch x with
       | (dlet x' : Z := 1 * (nth_default 0 ?f 0 * nth_default 0 ?g 0) in
   dlet x'0 : Z := x' + 0 in
   dlet x'1 : Z := x'0 / 2305843009213693952 in
   dlet x'2 : Z := x'0 mod 2305843009213693952 in
   dlet y' : Z := 1 * x'1 in
   dlet y'0 : Z := 1 * x'2 in
   dlet x'3 : Z := 1 * (y'0 + 0) in
   dlet x'4 : Z := 1 * (1 * (y' + 0)) in
   dlet x'5 : Z := x'3 + (x'4 + 0) in
   dlet x'6 : Z := x'5 / 2305843009213693952 in
   dlet x'7 : Z := x'5 mod 2305843009213693952 in
   dlet x'8 : Z := 1 * x'6 in
   dlet x'9 : Z := 1 * x'7 in
   dlet x'10 : Z := 1 * (x'9 + 0) in
   dlet x'11 : Z := 1 * (1 * (x'8 + 0)) in
   dlet x'12 : Z := 1 * (x'10 + (x'11 + 0)) in
   dlet y'1 : Z := 1 * (x'12 + 0) in
   dlet x'13 : Z := 0 in
                         [y'1 + (x'13 + 0)])
         => idtac
       | _ => fail 0 "Invalid result:" x
       end
  end.
Abort.

Goal True. time "goal_of_size 1" try assert (goal_of_size 1) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
(* Tactic call goal_of_size 1 ran for 11.346 secs (11.314u,0.031s) (success) *)
(*
Goal True. time "goal_of_size 2" try assert (goal_of_size 2) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
(* Tactic call goal_of_size 2 ran for 93.915 secs (93.807u,0.107s) (success) *)
Goal True. time "goal_of_size 3" try assert (goal_of_size 3) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
(* Tactic call goal_of_size 3 ran for 559.433 secs (558.805u,0.627s) (success) *)
Goal True. time "goal_of_size 4" try assert (goal_of_size 4) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
(* Tactic call goal_of_size 4 ran for 4363.725 secs (4359.384u,4.356s) (success) *)
Goal True. time "goal_of_size 5" try assert (goal_of_size 5) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
(* stack overflow *)
Goal True. time "goal_of_size 6" try assert (goal_of_size 5) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
Goal True. time "goal_of_size 7" try assert (goal_of_size 5) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
Goal True. time "goal_of_size 8" try assert (goal_of_size 5) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
Goal True. time "goal_of_size 9" try assert (goal_of_size 9) by (once (ViaRewriteStrat.go; print_goal ())). Abort.
*)
  (* Tactic call ran for 0.125 secs (0.125u,0.s) (success)
Tactic call ran for 0.015 secs (0.015u,0.s) (success)
Tactic call ran for 0.001 secs (0.001u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0.118 secs (0.114u,0.003s) (success)
Tactic call ran for 0.001 secs (0.001u,0.s) (success)
Tactic call ran for 1.151 secs (1.151u,0.s) (success)
Tactic call ran for 4.506 secs (4.494u,0.011s) (success)
Tactic call ran for 0.003 secs (0.003u,0.s) (success)
Tactic call ran for 1.008 secs (1.008u,0.s) (success)
Tactic call ran for 0.83 secs (0.83u,0.s) (success)
Tactic call ran for 0.003 secs (0.003u,0.s) (success)
Tactic call ran for 3.565 secs (3.549u,0.015s) (success)
Tactic call ran for 0.007 secs (0.007u,0.s) (success)
Goal:
((dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
  dlet x'0 : Z := x' + 0 in
  dlet x'1 : Z := x'0 / 2305843009213693952 in
  dlet x'2 : Z := x'0 mod 2305843009213693952 in
  dlet y' : Z := 1 * x'1 in
  dlet y'0 : Z := 1 * x'2 in
  dlet x'3 : Z := 1 * (y'0 + 0) in
  dlet x'4 : Z := 1 * (1 * (y' + 0)) in
  dlet x'5 : Z := x'3 + (x'4 + 0) in
  dlet x'6 : Z := x'5 / 2305843009213693952 in
  dlet x'7 : Z := x'5 mod 2305843009213693952 in
  dlet x'8 : Z := 1 * x'6 in
  dlet x'9 : Z := 1 * x'7 in
  dlet x'10 : Z := 1 * (x'9 + 0) in
  dlet x'11 : Z := 1 * (1 * (x'8 + 0)) in
  dlet x'12 : Z := 1 * (x'10 + (x'11 + 0)) in
  dlet y'1 : Z := 1 * (x'12 + 0) in
  dlet x'13 : Z := 0 in
  [y'1 + (x'13 + 0)]) = f)
Tactic call goal_of_size 1 ran for 11.346 secs (11.314u,0.031s) (success)
Chars 35942 - 36038 [(time~"goal_of_size~1"~~~try~~...] 11.346 secs (11.314u,0.031s)
Tactic call ran for 3.922 secs (3.906u,0.015s) (success)
Tactic call ran for 0.294 secs (0.294u,0.s) (success)
Tactic call ran for 0.003 secs (0.003u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 0.36 secs (0.36u,0.s) (success)
Tactic call ran for 0.002 secs (0.002u,0.s) (success)
Tactic call ran for 3.376 secs (3.372u,0.003s) (success)
Tactic call ran for 18.768 secs (18.752u,0.016s) (success)
Tactic call ran for 0.006 secs (0.006u,0.s) (success)
Tactic call ran for 5.973 secs (5.965u,0.007s) (success)
Tactic call ran for 4.171 secs (4.159u,0.011s) (success)
Tactic call ran for 0.007 secs (0.007u,0.s) (success)
Tactic call ran for 54.441 secs (54.401u,0.039s) (success)
Tactic call ran for 2.575 secs (2.563u,0.011s) (success)
Goal:
((dlet y' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
  dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 1) in
  dlet x'0 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 0) in
  dlet x'1 : Z := 2 * (1 * (nth_default 0 f 1 * nth_default 0 g 1)) in
  dlet x'2 : Z := y' + (x'1 + 0) in
  dlet x'3 : Z := x'2 / 18014398509481984 in
  dlet x'4 : Z := x'2 mod 18014398509481984 in
  dlet y'0 : Z := 1 * x'3 in
  dlet y'1 : Z := 1 * x'4 in
  dlet y'2 : Z := 1 * (x' + (x'0 + 0)) in
  dlet x'5 : Z := 1 * (y'1 + 0) in
  dlet x'6 : Z := 1 * (y'0 + (y'2 + 0)) in
  dlet x'7 : Z := 0 in
  dlet x'8 : Z := x'6 + 0 in
  dlet x'9 : Z := x'8 / 9007199254740992 in
  dlet x'10 : Z := x'8 mod 9007199254740992 in
  dlet x'11 : Z := 1 * (x'5 + (x'7 + 0)) in
  dlet x'12 : Z := 1 * x'9 in
  dlet x'13 : Z := 1 * x'10 in
  dlet x'14 : Z := 1 * (x'11 + 0) in
  dlet x'15 : Z := 1 * (x'13 + 0) in
  dlet x'16 : Z := 1 * (1 * (x'12 + 0)) in
  dlet x'17 : Z := x'14 + (x'16 + 0) in
  dlet x'18 : Z := x'17 / 18014398509481984 in
  dlet x'19 : Z := x'17 mod 18014398509481984 in
  dlet x'20 : Z := 1 * x'18 in
  dlet x'21 : Z := 1 * x'19 in
  dlet x'22 : Z := 1 * (x'15 + 0) in
  dlet x'23 : Z := 1 * (x'21 + 0) in
  dlet x'24 : Z := 1 * (x'20 + (x'22 + 0)) in
  dlet x'25 : Z := 0 in
  dlet x'26 : Z := x'24 + 0 in
  dlet x'27 : Z := x'26 / 9007199254740992 in
  dlet x'28 : Z := x'26 mod 9007199254740992 in
  dlet x'29 : Z := 1 * (x'23 + (x'25 + 0)) in
  dlet x'30 : Z := 1 * x'27 in
  dlet x'31 : Z := 1 * x'28 in
  dlet y'3 : Z := 1 * (x'29 + 0) in
  dlet y'4 : Z := 1 * (x'31 + 0) in
  dlet x'32 : Z := 1 * (1 * (x'30 + 0)) in
  [y'3 + (x'32 + 0); y'4 + 0]) = f)
Tactic call goal_of_size 2 ran for 93.915 secs (93.807u,0.107s) (success)
Chars 36121 - 36217 [(time~"goal_of_size~2"~~~try~~...] 93.915 secs (93.807u,0.107s)
Tactic call ran for 86.089 secs (85.885u,0.203s) (success)
Tactic call ran for 2.465 secs (2.461u,0.004s) (success)
Tactic call ran for 0.007 secs (0.007u,0.s) (success)
Tactic call ran for 0. secs (0.u,0.s) (success)
Tactic call ran for 1.163 secs (1.159u,0.003s) (success)
Tactic call ran for 0.003 secs (0.003u,0.s) (success)
Tactic call ran for 10.188 secs (10.152u,0.035s) (success)
Tactic call ran for 72.23 secs (72.122u,0.107s) (success)
Tactic call ran for 0.009 secs (0.009u,0.s) (success)
Tactic call ran for 28.633 secs (28.613u,0.019s) (success)
Tactic call ran for 18.459 secs (18.451u,0.007s) (success)
Tactic call ran for 0.014 secs (0.014u,0.s) (success)
Tactic call ran for 328.064 secs (327.832u,0.231s) (success)
Tactic call ran for 12.087 secs (12.075u,0.012s) (success)
Goal:
((dlet y' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
  dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 1) in
  dlet x'0 : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 2) in
  dlet x'1 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 0) in
  dlet x'2 : Z := 2 * (nth_default 0 f 1 * nth_default 0 g 1) in
  dlet x'3 : Z := 1 * (nth_default 0 f 2 * nth_default 0 g 0) in
  dlet x'4 : Z := 2 * (1 * (nth_default 0 f 1 * nth_default 0 g 2)) in
  dlet x'5 : Z := 2 * (1 * (nth_default 0 f 2 * nth_default 0 g 1)) in
  dlet x'6 : Z := 1 * (1 * (nth_default 0 f 2 * nth_default 0 g 2)) in
  dlet x'7 : Z := y' + (x'4 + (x'5 + 0)) in
  dlet x'8 : Z := x'7 / 8796093022208 in
  dlet x'9 : Z := x'7 mod 8796093022208 in
  dlet y'0 : Z := 1 * x'8 in
  dlet y'1 : Z := 1 * x'9 in
  dlet y'2 : Z := 1 * (x' + (x'1 + (x'6 + 0))) in
  dlet y'3 : Z := 1 * (x'0 + (x'2 + (x'3 + 0))) in
  dlet x'10 : Z := 1 * (y'1 + 0) in
  dlet x'11 : Z := 1 * (y'0 + (y'2 + 0)) in
  dlet x'12 : Z := 1 * (y'3 + 0) in
  dlet x'13 : Z := 0 in
  dlet x'14 : Z := x'11 + 0 in
  dlet x'15 : Z := x'14 / 4398046511104 in
  dlet x'16 : Z := x'14 mod 4398046511104 in
  dlet x'17 : Z := 1 * (x'10 + (x'13 + 0)) in
  dlet x'18 : Z := 1 * x'15 in
  dlet x'19 : Z := 1 * x'16 in
  dlet x'20 : Z := 1 * (x'12 + 0) in
  dlet x'21 : Z := 1 * (x'17 + 0) in
  dlet x'22 : Z := 1 * (x'19 + 0) in
  dlet x'23 : Z := 1 * (x'18 + (x'20 + 0)) in
  dlet x'24 : Z := 0 in
  dlet x'25 : Z := x'23 + 0 in
  dlet x'26 : Z := x'25 / 4398046511104 in
  dlet x'27 : Z := x'25 mod 4398046511104 in
  dlet x'28 : Z := 1 * (x'21 + (x'24 + 0)) in
  dlet x'29 : Z := 1 * (x'22 + 0) in
  dlet x'30 : Z := 1 * x'26 in
  dlet x'31 : Z := 1 * x'27 in
  dlet x'32 : Z := 1 * (x'28 + 0) in
  dlet x'33 : Z := 1 * (x'29 + 0) in
  dlet x'34 : Z := 1 * (x'31 + 0) in
  dlet x'35 : Z := 1 * (1 * (x'30 + 0)) in
  dlet x'36 : Z := x'32 + (x'35 + 0) in
  dlet x'37 : Z := x'36 / 8796093022208 in
  dlet x'38 : Z := x'36 mod 8796093022208 in
  dlet x'39 : Z := 1 * x'37 in
  dlet x'40 : Z := 1 * x'38 in
  dlet x'41 : Z := 1 * (x'33 + 0) in
  dlet x'42 : Z := 1 * (x'34 + 0) in
  dlet x'43 : Z := 1 * (x'40 + 0) in
  dlet x'44 : Z := 1 * (x'39 + (x'41 + 0)) in
  dlet x'45 : Z := 1 * (x'42 + 0) in
  dlet x'46 : Z := 0 in
  dlet x'47 : Z := x'44 + 0 in
  dlet x'48 : Z := x'47 / 4398046511104 in
  dlet x'49 : Z := x'47 mod 4398046511104 in
  dlet x'50 : Z := 1 * (x'43 + (x'46 + 0)) in
  dlet x'51 : Z := 1 * x'48 in
  dlet x'52 : Z := 1 * x'49 in
  dlet x'53 : Z := 1 * (x'45 + 0) in
  dlet y'4 : Z := 1 * (x'50 + 0) in
  dlet y'5 : Z := 1 * (x'52 + 0) in
  dlet x'54 : Z := 1 * (x'51 + (x'53 + 0)) in
  dlet x'55 : Z := 0 in
  [y'4 + (x'55 + 0); y'5 + 0; x'54 + 0]) = f)
Tactic call goal_of_size 3 ran for 559.433 secs (558.805u,0.627s) (success)
Chars 36220 - 36316 [(time~"goal_of_size~3"~~~try~~...] 559.433 secs (558.805u,0.627s)
Tactic call ran for 1862.263 secs (1859.248u,3.024s) (success)
Tactic call ran for 16.616 secs (16.576u,0.04s) (success)
Tactic call ran for 0.023 secs (0.023u,0.s) (success)
Tactic call ran for 0.001 secs (0.001u,0.s) (success)
Tactic call ran for 5.231 secs (5.231u,0.s) (success)
Tactic call ran for 0.004 secs (0.004u,0.s) (success)
Tactic call ran for 41.886 secs (41.846u,0.039s) (success)
Tactic call ran for 332.166 secs (331.758u,0.407s) (success)
Tactic call ran for 0.018 secs (0.018u,0.s) (success)
Tactic call ran for 148.93 secs (148.81u,0.119s) (success)
Tactic call ran for 94.186 secs (94.122u,0.063s) (success)
Tactic call ran for 0.031 secs (0.031u,0.s) (success)
Tactic call ran for 1810.372 secs (1809.722u,0.656s) (success)
Tactic call ran for 51.968 secs (51.964u,0.004s) (success)
Goal:
((dlet y' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
  dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 1) in
  dlet x'0 : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 2) in
  dlet x'1 : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 3) in
  dlet x'2 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 0) in
  dlet x'3 : Z := 2 * (nth_default 0 f 1 * nth_default 0 g 1) in
  dlet x'4 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 2) in
  dlet x'5 : Z := 1 * (nth_default 0 f 2 * nth_default 0 g 0) in
  dlet x'6 : Z := 1 * (nth_default 0 f 2 * nth_default 0 g 1) in
  dlet x'7 : Z := 1 * (nth_default 0 f 3 * nth_default 0 g 0) in
  dlet x'8 : Z := 2 * (11 * (nth_default 0 f 1 * nth_default 0 g 3)) in
  dlet x'9 : Z := 1 * (11 * (nth_default 0 f 2 * nth_default 0 g 2)) in
  dlet x'10 : Z := 1 * (11 * (nth_default 0 f 2 * nth_default 0 g 3)) in
  dlet x'11 : Z := 2 * (11 * (nth_default 0 f 3 * nth_default 0 g 1)) in
  dlet x'12 : Z := 1 * (11 * (nth_default 0 f 3 * nth_default 0 g 2)) in
  dlet x'13 : Z := 2 * (11 * (nth_default 0 f 3 * nth_default 0 g 3)) in
  dlet x'14 : Z := y' + (x'8 + (x'9 + (x'11 + 0))) in
  dlet x'15 : Z := x'14 / 281474976710656 in
  dlet x'16 : Z := x'14 mod 281474976710656 in
  dlet y'0 : Z := 1 * x'15 in
  dlet y'1 : Z := 1 * x'16 in
  dlet y'2 : Z := 1 * (x' + (x'2 + (x'10 + (x'12 + 0)))) in
  dlet y'3 : Z := 1 * (x'0 + (x'3 + (x'5 + (x'13 + 0)))) in
  dlet y'4 : Z := 1 * (x'1 + (x'4 + (x'6 + (x'7 + 0)))) in
  dlet x'17 : Z := 1 * (y'1 + 0) in
  dlet x'18 : Z := 1 * (y'0 + (y'2 + 0)) in
  dlet x'19 : Z := 1 * (y'3 + 0) in
  dlet x'20 : Z := 1 * (y'4 + 0) in
  dlet x'21 : Z := 0 in
  dlet x'22 : Z := x'18 + 0 in
  dlet x'23 : Z := x'22 / 140737488355328 in
  dlet x'24 : Z := x'22 mod 140737488355328 in
  dlet x'25 : Z := 1 * (x'17 + (x'21 + 0)) in
  dlet x'26 : Z := 1 * x'23 in
  dlet x'27 : Z := 1 * x'24 in
  dlet x'28 : Z := 1 * (x'19 + 0) in
  dlet x'29 : Z := 1 * (x'20 + 0) in
  dlet x'30 : Z := 1 * (x'25 + 0) in
  dlet x'31 : Z := 1 * (x'27 + 0) in
  dlet x'32 : Z := 1 * (x'26 + (x'28 + 0)) in
  dlet x'33 : Z := 1 * (x'29 + 0) in
  dlet x'34 : Z := 0 in
  dlet x'35 : Z := x'32 + 0 in
  dlet x'36 : Z := x'35 / 281474976710656 in
  dlet x'37 : Z := x'35 mod 281474976710656 in
  dlet x'38 : Z := 1 * (x'30 + (x'34 + 0)) in
  dlet x'39 : Z := 1 * (x'31 + 0) in
  dlet x'40 : Z := 1 * x'36 in
  dlet x'41 : Z := 1 * x'37 in
  dlet x'42 : Z := 1 * (x'33 + 0) in
  dlet x'43 : Z := 1 * (x'38 + 0) in
  dlet x'44 : Z := 1 * (x'39 + 0) in
  dlet x'45 : Z := 1 * (x'41 + 0) in
  dlet x'46 : Z := 1 * (x'40 + (x'42 + 0)) in
  dlet x'47 : Z := 0 in
  dlet x'48 : Z := x'46 + 0 in
  dlet x'49 : Z := x'48 / 140737488355328 in
  dlet x'50 : Z := x'48 mod 140737488355328 in
  dlet x'51 : Z := 1 * (x'43 + (x'47 + 0)) in
  dlet x'52 : Z := 1 * (x'44 + 0) in
  dlet x'53 : Z := 1 * (x'45 + 0) in
  dlet x'54 : Z := 1 * x'49 in
  dlet x'55 : Z := 1 * x'50 in
  dlet x'56 : Z := 1 * (x'51 + 0) in
  dlet x'57 : Z := 1 * (x'52 + 0) in
  dlet x'58 : Z := 1 * (x'53 + 0) in
  dlet x'59 : Z := 1 * (x'55 + 0) in
  dlet x'60 : Z := 1 * (11 * (x'54 + 0)) in
  dlet x'61 : Z := x'56 + (x'60 + 0) in
  dlet x'62 : Z := x'61 / 281474976710656 in
  dlet x'63 : Z := x'61 mod 281474976710656 in
  dlet x'64 : Z := 1 * x'62 in
  dlet x'65 : Z := 1 * x'63 in
  dlet x'66 : Z := 1 * (x'57 + 0) in
  dlet x'67 : Z := 1 * (x'58 + 0) in
  dlet x'68 : Z := 1 * (x'59 + 0) in
  dlet x'69 : Z := 1 * (x'65 + 0) in
  dlet x'70 : Z := 1 * (x'64 + (x'66 + 0)) in
  dlet x'71 : Z := 1 * (x'67 + 0) in
  dlet x'72 : Z := 1 * (x'68 + 0) in
  dlet x'73 : Z := 0 in
  dlet x'74 : Z := x'70 + 0 in
  dlet x'75 : Z := x'74 / 140737488355328 in
  dlet x'76 : Z := x'74 mod 140737488355328 in
  dlet x'77 : Z := 1 * (x'69 + (x'73 + 0)) in
  dlet x'78 : Z := 1 * x'75 in
  dlet x'79 : Z := 1 * x'76 in
  dlet x'80 : Z := 1 * (x'71 + 0) in
  dlet x'81 : Z := 1 * (x'72 + 0) in
  dlet y'5 : Z := 1 * (x'77 + 0) in
  dlet y'6 : Z := 1 * (x'79 + 0) in
  dlet x'82 : Z := 1 * (x'78 + (x'80 + 0)) in
  dlet x'83 : Z := 1 * (x'81 + 0) in
  dlet x'84 : Z := 0 in
  [y'5 + (x'84 + 0); y'6 + 0; x'82 + 0; x'83 + 0]) = f)
Tactic call goal_of_size 4 ran for 4363.725 secs (4359.384u,4.356s) (success)
Chars 36527 - 36623 [(time~"goal_of_size~4"~~~try~~...] 4363.725 secs (4359.384u,4.356s)
Chars 36631 - 36641 [Goal~_~True.] 0. secs (0.u,0.s)
Chars 36642 - 36738 [(time~"goal_of_size~5"~~~try~~...] 31132.252 secs (31123.835u,8.56s)
*)

Set Ltac Profiling.
Set Printing Depth 1000000.
Set Typeclasses Debug.
Set Printing Width 1000000.

(* sanity check *)
Goal True.
  assert (goal_of_size 1).
  ViaSetoidRewrite.go.
  lazymatch goal with
  | [ |- ?x = _ ]
    => lazymatch x with
       | (dlet x' : Z := 1 * (nth_default 0 ?f 0 * nth_default 0 ?g 0) in
   dlet x'0 : Z := x' + 0 in
   dlet x'1 : Z := x'0 / 2305843009213693952 in
   dlet x'2 : Z := x'0 mod 2305843009213693952 in
   dlet y' : Z := 1 * x'1 in
   dlet y'0 : Z := 1 * x'2 in
   dlet x'3 : Z := 1 * (y'0 + 0) in
   dlet x'4 : Z := 1 * (1 * (y' + 0)) in
   dlet x'5 : Z := x'3 + (x'4 + 0) in
   dlet x'6 : Z := x'5 / 2305843009213693952 in
   dlet x'7 : Z := x'5 mod 2305843009213693952 in
   dlet x'8 : Z := 1 * x'6 in
   dlet x'9 : Z := 1 * x'7 in
   dlet x'10 : Z := 1 * (x'9 + 0) in
   dlet x'11 : Z := 1 * (1 * (x'8 + 0)) in
   dlet x'12 : Z := 1 * (x'10 + (x'11 + 0)) in
   dlet y'1 : Z := 1 * (x'12 + 0) in
   dlet x'13 : Z := 0 in
                         [y'1 + (x'13 + 0)])
         => idtac
       | _ => fail 0 "Invalid result:" x
       end
  end.
Abort.

(* via setoid_rewrite *)
Goal goal.
  Time ViaSetoidRewrite.go.
  Time Optimize Proof.
  Time Optimize Heap.
  (*
    Time ViaSetoidRewrite.go_count_max O constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time ViaSetoidRewrite.go_count_max constr:(1000%nat) constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time ViaSetoidRewrite.go_count_max constr:(2000%nat) constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time ViaSetoidRewrite.go_count constr:(3000%nat).
     *)
    (* size 1: Finished transaction in 100.141 secs (99.967u,0.171s) (successful) *)
    (* Size 2: Finished transaction in 607.765 secs (606.448u,1.267s) (successful), Finished: 1269%nat *)
    (* size 3: Finished transaction in 8706.089 secs (8692.561u,13.515s) (successful), Finished: 2398%nat, src/Rewriter/PerfTesting/fiat_crypto_via_rewrite_strat.vo (real: 8711.19, user: 8695.54, sys: 15.63, mem: 58206840 ko) *)
    (* size 4: Fatal error: out of memory.
Command exited with non-zero status 2
src/Rewriter/PerfTesting/fiat_crypto_via_rewrite_strat.vo (real: 7473.28, user: 7459.76, sys: 13.31, mem: 52415844 ko) *)

    (* Size 3 end:
Goal: ((dlet y' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
        dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 1) in
        dlet x'0 : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 2) in
        dlet x'1 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 0) in
        dlet x'2 : Z := 2 * (nth_default 0 f 1 * nth_default 0 g 1) in
        dlet x'3 : Z := 1 * (nth_default 0 f 2 * nth_default 0 g 0) in
        dlet x'4 : Z := 2 * (5 * (nth_default 0 f 1 * nth_default 0 g 2)) in
        dlet x'5 : Z := 2 * (5 * (nth_default 0 f 2 * nth_default 0 g 1)) in
        dlet x'6 : Z := 1 * (5 * (nth_default 0 f 2 * nth_default 0 g 2)) in
        dlet x'7 : Z := y' + (x'4 + (x'5 + 0)) in
        dlet x'8 : Z := x'7 / 17592186044416 in
        dlet x'9 : Z := x'7 mod 17592186044416 in
        dlet y'0 : Z := 1 * x'8 in
        dlet y'1 : Z := 1 * x'9 in
        dlet y'2 : Z := 1 * (x' + (x'1 + (x'6 + 0))) in
        dlet y'3 : Z := 1 * (x'0 + (x'2 + (x'3 + 0))) in
        dlet y'4 : Z := 1 * (y'1 + 0) in
        dlet y'5 : Z := 1 * (y'0 + (y'2 + 0)) in
        dlet y'6 : Z := 1 * (y'3 + 0) in
        dlet y'7 : Z := 0 in
        dlet y'8 : Z := 1 * (y'4 + (y'7 + 0)) in
        dlet x'10 : Z := y'5 + 0 in
        dlet x'11 : Z := x'10 / 8796093022208 in
        dlet x'12 : Z := x'10 mod 8796093022208 in
        dlet y'9 : Z := 1 * x'11 in
        dlet y'10 : Z := 1 * x'12 in
        dlet y'11 : Z := 1 * (y'6 + 0) in
        dlet y'12 : Z := 1 * (y'8 + 0) in
        dlet y'13 : Z := 1 * (y'10 + 0) in
        dlet y'14 : Z := 1 * (y'9 + (y'11 + 0)) in
        dlet y'15 : Z := 0 in
        dlet y'16 : Z := 1 * (y'12 + (y'15 + 0)) in
        dlet y'17 : Z := 1 * (y'13 + 0) in
        dlet x'13 : Z := y'14 + 0 in
        dlet x'14 : Z := x'13 / 8796093022208 in
        dlet x'15 : Z := x'13 mod 8796093022208 in
        dlet y'18 : Z := 1 * x'14 in
        dlet y'19 : Z := 1 * x'15 in
        dlet y'20 : Z := 1 * (y'16 + 0) in
        dlet y'21 : Z := 1 * (y'17 + 0) in
        dlet y'22 : Z := 1 * (y'19 + 0) in
        dlet y'23 : Z := 1 * (5 * (y'18 + 0)) in
        dlet x'16 : Z := y'20 + (y'23 + 0) in
        dlet x'17 : Z := x'16 / 17592186044416 in
        dlet x'18 : Z := x'16 mod 17592186044416 in
        dlet y'24 : Z := 1 * x'17 in
        dlet y'25 : Z := 1 * x'18 in
        dlet y'26 : Z := 1 * (y'21 + 0) in
        dlet y'27 : Z := 1 * (y'22 + 0) in
        dlet y'28 : Z := 1 * (y'25 + 0) in
        dlet y'29 : Z := 1 * (y'24 + (y'26 + 0)) in
        dlet y'30 : Z := 1 * (y'27 + 0) in
        dlet y'31 : Z := 0 in
        dlet y'32 : Z := 1 * (y'28 + (y'31 + 0)) in
        dlet x'19 : Z := y'29 + 0 in
        dlet x'20 : Z := x'19 / 8796093022208 in
        dlet x'21 : Z := x'19 mod 8796093022208 in
        dlet y'33 : Z := 1 * x'20 in
        dlet y'34 : Z := 1 * x'21 in
        dlet y'35 : Z := 1 * (y'30 + 0) in
        dlet y'36 : Z := 1 * (y'32 + 0) in
        dlet y'37 : Z := 1 * (y'34 + 0) in
        dlet y'38 : Z := 1 * (y'33 + (y'35 + 0)) in
        dlet y'39 : Z := 0 in
        [y'36 + (y'39 + 0); y'37 + 0; y'38 + 0]) = f)
*)
    Show.
Abort.
(*
    Time
    Show.
Abort.
*)
