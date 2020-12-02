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
Hint Rewrite lift_dlet : mydb letdb.
Lemma lift_dlet1 A B C D x y (f : A -> B) (g : B -> C -> D) : g (Let_In x f) y = Let_In x (fun x' => g (f x') y). Proof. reflexivity. Qed.
Hint Rewrite lift_dlet1 : mydb letdb.
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
Proof. repeat intro; subst; apply flat_map_ext; auto. Qed.

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

Class params :=
  { n : nat;
    s : Z;
    c : list (Z * Z);
    idxs : list nat;
    limbwidth := (inject_Z (Z.log2_up (s - Associational.eval c)) / inject_Z (Z.of_nat n))%Q;
    machine_wordsize : Z }.
(*
Require Import Crypto.Rewriter.PerfTesting.Core.
Import UnsaturatedSolinas.
Definition p' := Eval vm_compute in of_string "2^61 - 1" 64.
Definition p : params
  := Eval vm_compute in invert_Some (List.nth_error p' 0).
Print p.
 *)
Notation size_of_problem := 1%nat (only parsing).
Definition p : params
  := match size_of_problem as n return match n with 4%nat => _ | _ => _ end with
     | 1%nat => (* 2^61-1, 1 limb *)
       {| n := 1; s := 2305843009213693952; c := [(1, 1)]; idxs := [0%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 2%nat => (* 2^107-1, 2 limbs *)
       {| n := 2; s := 162259276829213363391578010288128; c := [(1, 1)]; idxs := [0%nat; 1%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 3%nat => (* 2^127-1, 3 limbs *)
       {| n := 3; s := 170141183460469231731687303715884105728; c := [(1, 1)]; idxs := [0%nat; 1%nat; 2%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | 4%nat => (* 2^190-11, 4 limbs *)
       {| n := 4; s := 1569275433846670190958947355801916604025588861116008628224; c := [(1, 11)]; idxs := [0%nat; 1%nat; 2%nat; 3%nat; 0%nat; 1%nat]; machine_wordsize := 64 |}
     | _ => (* no recorded example *) tt
     end.
Existing Instance p.
Goal True.
  pose (fun f g : list Z => ModOps.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (expand_list 0 f n) (expand_list 0 g n)) as v.
  cbv -[ModOps.carry_mulmod expand_list] in v.
  assert (forall f g, v f g = f); subst v; intros.
  { cbv [expand_list ModOps.carry_mulmod expand_list_helper nat_rect ModOps.weight Positional.mulmod Positional.to_associational seq List.map List.combine Associational.mul flat_map].
    Set Ltac Profiling.
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
    Ltac go_count n := go_count_max n tt.
    Ltac go := go_count O (*repeat go_step*).
    Set Printing Depth 1000000.
    Set Typeclasses Debug.
    Time go.
    Time Optimize Proof.
    Time Optimize Heap.
    (*
    Time go_count_max O constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time go_count_max constr:(1000%nat) constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time go_count_max constr:(2000%nat) constr:(1000%nat).
    Time Optimize Proof.
    Time Optimize Heap.
    Time go_count constr:(3000%nat).
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
    Time (rewrite_strat (((topdown (hints mydb; eval mycbv));
                            eval cbv [Associational.repeat_reduce nat_rect Associational.split Associational.mul];
                            ((topdown (hints mydb; eval mycbv)));
                            eval cbv [Positional.from_associational Init.Nat.pred Positional.zeros repeat Positional.place nat_rect Positional.add_to_nth])));
      (* COQBUG(https://github.com/coq/coq/issues/10934) *)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Positional.chained_carries Positional.carry_reduce]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Positional.carry Positional.to_associational Associational.carry seq Associational.carryterm Positional.from_associational]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat eval cbv [Init.Nat.pred Positional.zeros repeat Positional.place nat_rect]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Positional.add_to_nth Associational.reduce]);(*.
        Set Printing Depth 1000000.
        Typeclasses eauto := debug.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv))))).
    Show.
Abort.
*)
