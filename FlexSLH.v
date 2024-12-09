(** * FlexSLH: Selective Ultimate SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT UltimateSLH.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

Fixpoint vars_aexp (a:aexp) : list string :=
  match a with
  | ANum n => []
  | AId x => [x]
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ be ? a1 : a2 }> => vars_bexp be ++ vars_aexp a1 ++ vars_aexp a2
  end
with vars_bexp (a:bexp) : list string :=
  match a with
  | <{ true }> | <{ false }> => []
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ ~b }> => vars_bexp b
  | <{ b1 && b2 }> => vars_bexp b1 ++ vars_bexp b2
  end.

Fixpoint label_of_aexp (P:pub_vars) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId x => P x
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ be ? a1 : a2 }> => join (label_of_bexp P be) (join (label_of_aexp P a1) (label_of_aexp P a2))
  end
with label_of_bexp (P:pub_vars) (b:bexp) : label :=
  match b with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  end.

Ltac rewrite_eq :=
  match goal with
  | H:_=_ |- _ => rewrite H; clear H
  | H:forall _, _=_ |- _ => rewrite H; clear H
  | _ => idtac
 end.

Ltac invert H := inversion H; subst; clear H.

Definition AllPub : pub_vars := (_!-> public).
Definition AllSecret : pub_vars := (_!-> secret).

Fixpoint flex_slh (P:pub_vars) (c:com) : com :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ flex_slh P c1; flex_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{if be' then "b" := be' ? "b" : 1; flex_slh P c1
                   else "b" := be' ? 1 : "b"; flex_slh P c2 end}}>
  | <{{while be do c end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{while be' do "b" := be' ? "b" : 1; flex_slh P c end;
             "b" := be' ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    let i' := if label_of_aexp P i && negb (P x)
      then i
      else <{{("b" = 1) ? 0 : i}}> (* Ultimate SLH *)
    in <{{x <- a[[i']]}}>
(* Simplified this (TODO: prove it's equivalent to sel_addr_slh, which needs to be defined):
    if label_of_aexp P i
    then (* Selective SLH -- mask the value of public loads *)
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
                   else <{{x <- a[[i]]}}>
    else (* Ultimate SLH -- mask private address of load *)
      <{{x <- a[[("b" = 1) ? 0 : i]] }}>
*)
  | <{{a[i] <- e}}> =>
    let i' := if label_of_aexp P i && label_of_aexp P e
      then i (* Selective SLH -- no mask even if it's out of bounds! *)
      else <{{("b" = 1) ? 0 : i}}> (* Ultimate SLH *)
    in <{{a[i'] <- e}}> (* <- Doing nothing here in label_of_aexp P i = true case okay for Spectre v1,
                              but would be problematic for return address or code pointer overwrites *)
  end)%string.

Lemma label_of_exp_sound : forall P,
  (forall a, P |-a- a \in label_of_aexp P a) /\
  (forall b, P |-b- b \in label_of_bexp P b).
Proof. intro P. apply aexp_bexp_mutind; intros; now constructor. Qed.

Corollary label_of_aexp_sound : forall P a,
  P |-a- a \in label_of_aexp P a.
Proof. intros. apply label_of_exp_sound. Qed.

Corollary label_of_bexp_sound : forall P b,
  P |-b- b \in label_of_bexp P b.
Proof. intros. apply label_of_exp_sound. Qed.

Lemma label_of_exp_unique : forall P,
  (forall a l, P |-a- a \in l -> l = label_of_aexp P a) /\
  (forall b l, P |-b- b \in l -> l = label_of_bexp P b).
Proof. intro P. apply aexp_bexp_has_label_mutind; intros; (repeat rewrite_eq); reflexivity. Qed.

Corollary label_of_aexp_unique : forall P a l,
  P |-a- a \in l ->
  l = label_of_aexp P a.
Proof. intro. apply label_of_exp_unique. Qed.

Corollary label_of_bexp_unique : forall P b l,
  P |-b- b \in l ->
  l = label_of_bexp P b.
Proof. intro. apply label_of_exp_unique. Qed.

Corollary aexp_has_label_inj : forall P a l l',
  P |-a- a \in l ->
  P |-a- a \in l' ->
  l = l'.
Proof. intros. apply label_of_aexp_unique in H, H0. now rewrite_eq. Qed.

Corollary bexp_has_label_inj : forall P b l l',
  P |-b- b \in l ->
  P |-b- b \in l' ->
  l = l'.
Proof. intros. apply label_of_bexp_unique in H, H0. now rewrite_eq. Qed.

(* For CT programs this is the same as sel_slh *)

Module RelatingSelSLH.

  Lemma sel_slh_is_flex_slh : forall P PA c,
      ct_well_typed P PA c ->
      sel_slh P c = flex_slh P c.
  Proof.
    intros P PA c H. induction H; simpl; repeat rewrite_eq; try reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. 
  Abort.
  (* reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
  Qed. *)

End RelatingSelSLH.

(* The following standard IFC type system that just tracks explicit and implicit
   flows seems good enough for what we need. Most importantly, it gives us
   noninterference both sequentially and speculatively after applying flex_slh
   (see testing below). *)

Reserved Notation "P '&' PA ',' pc '|--' c" (at level 40).

Inductive well_typed (P PA : pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P & PA, pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \in l ->
      can_flow (join pc l) (P X) = true ->
      P & PA, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P & PA, pc |-- c1 ->
      P & PA, pc |-- c2 ->
      P & PA, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \in l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, (join pc l) |-- c2 ->
      P & PA, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \in l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, pc |-- <{ while b do c1 end }>
  | WT_ARead : forall pc x a i li,
      P |-a- i \in li ->
      can_flow (join pc (join li (PA a))) (P x) = true ->
      P & PA, pc |-- <{{ x <- a[[i]] }}>
  | WT_AWrite : forall pc a i e li l,
      P |-a- i \in li ->
      P |-a- e \in l ->
      can_flow (join pc (join li l)) (PA a) = true ->
      P & PA, pc |-- <{{ a[i] <- e }}>
where "P '&' PA ',' pc '|--' c" := (well_typed P PA pc c).

(** * Ideal small-step evaluation *)

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    pub_vars -> com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall P st ast b e n x,
      aeval st e = n ->
      P |- <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall P c1 st ast b ds os c1t stt astt bt c2,
      P |- <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      P |- <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall P st ast b c2,
      P |- <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall P be ct cf st ast b c' b' l,
      P |-b- be \in l ->
      b' = (l || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | ISM_If_F : forall P be ct cf st ast b c' b' l,
      P |-b- be \in l ->
      b' = (l || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | ISM_While : forall P be c st ast b,
      P |- <((while be do c end, st, ast, b))> -->i_[]^^[]
            <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall P x a ie st ast (b :bool) i li,
      P |-a- ie \in li ->
      (if (negb li || (P x)) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
            <((skip, x !-> (nth i (ast a) 0); st, ast, b))>
  | ISM_ARead_U : forall P x a ie st ast i a' i',
      aeval st ie = i ->
      P |-a- ie \in public ->
      P x = secret ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i]
            <((skip, x !-> (nth i' (ast a') 0); st, ast, true))>
  | ISM_Write : forall P a ie e st ast (b :bool) i n li le,
      aeval st e = n ->
      P |-a- ie \in li ->
      P |-a- e \in le ->
      (if (negb li || negb le) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
            <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | ISM_Write_U : forall P a ie e st ast i n a' i',
      aeval st e = n ->
      P |-a- ie \in public ->
      P |-a- e \in public ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((a[ie] <- e, st, ast, true))> -->i_[DStore a' i']^^[OAWrite a i]
            <((skip, st, a' !-> upd i' (ast a') n; ast, true))>

  where "P |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step P c st ast b ct stt astt bt ds os).

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (P:pub_vars) (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : P |- <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      P |- <((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      P |- <((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      P |- <((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

  where "P |- <(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal P c st ast b ct stt astt bt ds os).

Lemma multi_ideal_trans_nil_l P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_[]^^[] <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_[]^^[] <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    P |- <((c, st, ast, b))> -->i*_ds^^osm <((cm, stm, astm, bm))> ->
    P |- <((cm, stm, astm, bm))> -->i*_dsm^^ost <((ct, stt, astt, bt))> ->
    P |- <((c, st, ast, b))> -->i*_(ds++dsm)^^(osm++ost) <((ct, stt, astt, bt))>.
Proof.
  intros P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma multi_ideal_add_snd_com : forall P c st ast ct stt astt ds os c2 b bt,
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c;c2, st, ast, b))> -->i*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma ideal_eval_small_step_obs_length : forall P c st ast b ds ct stt astt bt os,
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof. intros. induction H; simpl; auto. Qed.

Lemma ideal_eval_small_step_same_length : forall P c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2,
  P |- <((c, st1, ast1, b1))> -->i_ds1^^os1 <((ct1, stt1, astt1, bt1))> ->
  P |- <((c, st2, ast2, b2))> -->i_ds2^^os2 <((ct2, stt2, astt2, bt2))> ->
  length ds1 = length ds2.
Proof.
  intros P c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2. intros. revert st2 ast2 b2 ct2 stt2 astt2 bt2 H0.
  induction H; simpl; intros.
  + now invert H0.
  + invert H0; [|inversion H].
    eapply IHideal_eval_small_step; eassumption.
  + invert H0; [inversion H12|reflexivity].
  + now invert H2.
  + now invert H2.
  + now invert H0.
  + now invert H2.
  + now invert H4.
  + now invert H4.
  + now invert H5.
Qed.

Lemma multi_ideal_obs_length : forall P c st ast b ds ct stt astt bt os,
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof. intros. induction H; [tauto|].
  do 2 rewrite app_length. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_eval_small_step_spec_bit_monotonic : forall P c st ast ds ct stt astt bt os,
  P |- <((c, st, ast, true))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall P c st ast ds ct stt astt bt os,
  P |- <((c, st, ast, true))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma wt_relax : forall P PA c,
  P & PA, secret |-- c ->
  P & PA, public |-- c.
Proof.
  intros. remember secret as pc. revert Heqpc. induction H; intros; subst; try now constructor.
  + econstructor; [eassumption|]. unfold can_flow, join, secret, public in *. simpl in H0. apply negb_true_iff in H0.
    rewrite H0. simpl. now rewrite orb_true_r.
  + constructor; tauto.
  + unfold join, secret in *. simpl in *. econstructor; [eassumption|unfold join, public; destruct l; tauto..].
  + econstructor; [eassumption|]. unfold join, public, secret in *. destruct l; tauto.
  + econstructor; [eassumption|]. unfold can_flow, join, public, secret in *. simpl in H0.
    apply negb_true_iff in H0. rewrite H0. simpl. now rewrite orb_true_r.
  + econstructor; [eassumption..|]. unfold can_flow, join, public, secret in *. simpl in H1.
    apply negb_true_iff in H1. rewrite H1. simpl. now rewrite orb_true_r.
Qed.

Lemma ideal_eval_small_step_preserves_wt : forall P PA c st ast b ct stt astt bt pc ds os,
  P & PA, pc |-- c ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  P & PA, pc |-- ct.
Proof.
  intros. induction H0; try now constructor.
  + invert H. constructor; tauto.
  + now invert H.
  + invert H. eapply bexp_has_label_inj in H0; [|eassumption]. subst. destruct pc.
    - unfold join in *. destruct l. { now destruct b, (beval st be). }
      simpl in *. fold secret in *. fold public. apply wt_relax in H8, H9. now destruct b, (beval st be).
    - unfold join in *. now destruct l, b, (beval st be).
  + invert H. eapply bexp_has_label_inj in H0; [|eassumption]. subst. destruct pc.
    - unfold join in *. destruct l. { now destruct b, (beval st be). }
      simpl in *. fold secret in *. fold public. apply wt_relax in H8, H9. now destruct b, (beval st be).
    - unfold join in *. now destruct l, b, (beval st be).
  + invert H. econstructor; [eassumption| |constructor]. constructor; [tauto|]. econstructor; [eassumption|].
    unfold join in *. now destruct pc, l.
Qed.

Lemma ideal_eval_small_step_preserves_pub_equiv : forall P PA c st1 st2 ast1 ast2 b ct stt1 stt2 astt1 astt2 bt pc ds os,
  P & PA, pc |-- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA ast1 ast2 ->
  P |- <((c, st1, ast1, b))> -->i_ds^^os <((ct, stt1, astt1, bt))> ->
  P |- <((c, st2, ast2, b))> -->i_ds^^os <((ct, stt2, astt2, bt))> ->
  pub_equiv P stt1 stt2 /\ pub_equiv PA astt1 astt2.
Proof.
  intros P PA c st1 st2 ast1 ast2 b ct stt1 stt2 astt1 astt2 bt pc ds os. intros. revert st2 ast2 stt2 astt2 H0 H1 H H3. induction H2; simpl; intros.
  + invert H3. split; [|tauto]. intros x' Hx'. case (String.eqb x x') eqn:Heq.
    - apply String.eqb_eq in Heq. subst. invert H2. unfold join, can_flow in H5. rewrite !t_update_eq.
      eapply noninterferent_aexp; [eassumption|]. destruct l; [now unfold public|]. rewrite Hx' in H6. now rewrite andb_false_r in H6.
    - apply String.eqb_neq in Heq. do 2 (rewrite t_update_neq; [|tauto]). now apply H0.
  + invert H3; [|inversion H2]. invert H. eapply IHideal_eval_small_step; eassumption.
  + now invert H3; [inversion H15|].
  + now invert H5.
  + now invert H5.
  + now invert H3.
  + invert H5. split; [|tauto]. eapply aexp_has_label_inj in H; [|eassumption]. subst.
    invert H4. unfold can_flow, join in H8. eapply aexp_has_label_inj in H14; [|eassumption]. subst.
    intros x' Hx'. destruct (String.eqb x x') eqn:Heq.
    - apply String.eqb_eq in Heq. subst. rewrite Hx', orb_false_r in H8. apply andb_prop in H8. destruct H8; subst.
      apply andb_prop in H0. destruct H0; subst. specialize (H3 a H0). now rewrite H3, !t_update_eq.
    - apply String.eqb_neq in Heq. do 2 (rewrite t_update_neq; [|tauto]). now apply H2.
  + invert H7. split; [|tauto]. intros x' Hx'. destruct (String.eqb x x') eqn:Heq.
    - apply String.eqb_eq in Heq. subst. rewrite H21 in Hx'. now unfold secret in Hx'.
    - apply String.eqb_neq in Heq. do 2 (rewrite t_update_neq; [|tauto]). now apply H4.
  + invert H7. split; [tauto|]. intros a' Ha'. destruct (a =? a') eqn:Heq.
    - apply String.eqb_eq in Heq. subst. rewrite !t_update_eq.
      specialize (H5 a' Ha'). invert H6. unfold can_flow, join in H11.
      eapply aexp_has_label_inj in H1; [|eassumption]. eapply aexp_has_label_inj in H0; [|eassumption]. subst.
      rewrite Ha' in H11. simpl in H11. rewrite orb_false_r in H11. apply andb_prop in H11. destruct H11. subst.
      apply andb_prop in H0. destruct H0. subst. pose proof (noninterferent_aexp H4 H10). now rewrite H5, H.
    - apply String.eqb_neq in Heq. do 2 (rewrite t_update_neq; [|tauto]). now apply H5.
  + invert H8. split; [tauto|]. intros a'' Ha''. destruct (a' =? a'') eqn:Heq.
    - apply String.eqb_eq in Heq. subst. rewrite !t_update_eq.
      pose proof (noninterferent_aexp H5 H1). specialize (H6 a'' Ha''). now rewrite H, H6.
    - apply String.eqb_neq in Heq. do 2 (rewrite t_update_neq; [|tauto]). now apply H6.
Qed.

Definition ideal_same_obs P c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((c1, stt1, astt1, bt1))> ->
    P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((c2, stt2, astt2, bt2))> ->
    os1 = os2.

Lemma t_update_nonempty_arrs : forall ast a i n,
  nonempty_arrs ast -> nonempty_arrs (a !-> upd i (ast a) n; ast).
Proof.
  intros ast a i n H a'.
  case (a =? a') eqn:Heq.
  + apply String.eqb_eq in Heq. rewrite Heq, t_update_eq, upd_length. now apply H.
  + apply String.eqb_neq in Heq. rewrite t_update_neq; [|tauto]. now apply H.
Qed.

Lemma ideal_eval_preserves_nonempty_arrs : forall P c st ast b ct stt astt bt ds os,
  nonempty_arrs ast ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  nonempty_arrs astt.
Proof.
  intros.
  induction H0; [tauto..|now apply t_update_nonempty_arrs|now apply t_update_nonempty_arrs].
Qed.

Lemma multi_ideal_preserves_nonempty_arrs : forall P c st ast b ct stt astt bt ds os,
  nonempty_arrs ast ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  nonempty_arrs astt.
Proof.
  intros. induction H0; [tauto|].
  apply ideal_eval_preserves_nonempty_arrs in H0; tauto.
Qed.

Lemma ideal_unused_overwrite : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, X !-> n; st, ast, b))> -->i_ds^^os <((ct, X !-> n; stt, astt, bt))> /\ unused X ct.
Proof.
  intros. induction H0; simpl in *.
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. constructor. now rewrite aeval_unused_update.
  + repeat constructor; tauto.
  + now repeat constructor.
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [eassumption|now rewrite beval_unused_update|tauto].
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [eassumption|now rewrite beval_unused_update|tauto].
  + now repeat constructor.
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [eassumption|now rewrite aeval_unused_update|tauto].
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [now rewrite aeval_unused_update|tauto..].
  + split; [|trivial]. econstructor. 2, 3, 5:eassumption. all:now rewrite aeval_unused_update.
  + split; [|trivial]. econstructor. 1, 4: now rewrite aeval_unused_update. all:tauto.
Qed.

Lemma multi_ideal_unused_overwrite : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((ct, X !-> n; stt, astt, bt))>.
Proof.
  intros. induction H0; [constructor|].
  eapply ideal_unused_overwrite in H0; [|eassumption].
  destruct H0. now econstructor; eauto.
Qed.

Lemma multi_ideal_unused_update : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((ct, X !-> n; stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, X !-> st X; stt, astt, bt))>.
Proof.
  intros. eapply multi_ideal_unused_overwrite with (n:=st X) in H0; [|eassumption].
  now rewrite !t_update_shadow, t_update_same in H0.
Qed.

Ltac solve_refl :=
  now eexists; split; [|(try discriminate); (try now repeat econstructor)]; rewrite ?t_update_shadow, t_update_same;
  repeat econstructor; (repeat rewrite_eq); rewrite ?andb_false_r; (try now apply label_of_exp_sound).

Lemma flex_slh_bcc_generalized : forall c ds P st ast (b:bool) c' st' ast' b' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((flex_slh P c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists c'', P |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st', ast', b'))> /\
    (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0)).
Proof.
  intros c ds P. eapply prog_size_ind with (c:=c) (ds:=ds). clear.
  intros c ds IH. intros until os. intros Harrs Hunused st_b H.
  destruct c; simpl in *.
  + invert H; [solve_refl|]. invert H0.
  + invert H; [solve_refl|]. invert H0. invert H1; [|inversion H]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
    eexists. repeat econstructor. rewrite t_update_neq; tauto.
  + apply multi_spec_seq in H. destruct H.
    - do 8 destruct H. destruct H0, H1. subst. apply IH in H1; [|prog_size_auto|tauto..]. destruct H1, H, H0; [reflexivity|]. subst.
      eapply multi_ideal_preserves_nonempty_arrs in Harrs; [|eassumption]. apply IH in H2; [|prog_size_auto|tauto..].
      destruct H2, H0. eexists. split; [|apply H2]. eapply multi_ideal_unused_overwrite with (X:="b") (n:=st "b") in H0; [|tauto].
      rewrite t_update_shadow in H0. eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|].
      eapply multi_ideal_trans_nil_l; [constructor|assumption].
    - do 2 destruct H. subst. apply IH in H0; [|prog_size_auto|tauto..]. destruct H0, H.
      eexists. split; [|discriminate]. apply multi_ideal_add_snd_com. eassumption.
  + invert H; [solve_refl|].
    invert H0.
    - destruct (beval st'0 be) eqn:Hbe.
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = label_of_bexp P be || negb b'0)
          by now destruct (label_of_bexp P be); simpl; rewrite ?st_b, Hbe; destruct b'0. rewrite Heq in *.
        destruct (label_of_bexp P be || negb b'0) eqn:Hlb_b.
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|].
           invert H; [inversion H12|]. simpl in H1. rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H. eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
           rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H. eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct (label_of_bexp P be); simpl; rewrite Hbe, ?andb_false_r. rewrite Heq in *.
        invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
        rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..]. destruct H1, H. eexists.
        split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq; rewrite andb_false_r|tauto].
    - destruct (beval st'0 be) eqn:Hbe.
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = label_of_bexp P be || negb b)
          by now destruct (label_of_bexp P be); simpl; rewrite ?st_b, Hbe; destruct b. rewrite Heq in *.
        destruct (label_of_bexp P be || negb b) eqn:Hlb_b.
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|].
           invert H; [inversion H12|]. simpl in H1. rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H. eexists. split; [|apply H0]. rewrite !app_nil_l. rewrite t_update_eq in H.
           apply multi_ideal_unused_update in H; [|tauto].
           repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
           rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..]. rewrite t_update_eq in H1.
           destruct H1, H. apply multi_ideal_unused_update in H; [|tauto].
           eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct (label_of_bexp P be); simpl; rewrite Hbe, ?andb_false_r. rewrite Heq in *.
        invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
        rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..]. destruct H1, H. eexists. rewrite t_update_eq in H.
        apply multi_ideal_unused_update in H; [|tauto].
        split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq; rewrite andb_false_r|tauto].
  + invert H; [solve_refl|]. invert H0. invert H12. invert H1; [solve_refl|]. invert H. invert H12.
    - destruct (beval st'1 be && (label_of_bexp P be || (st'1 "b" =? 0)%nat)) eqn:Heq.
      * apply andb_prop in Heq. destruct Heq. apply orb_prop in H1.
        assert (Heq : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct H1 as [->|H1], (label_of_bexp P be); simpl; repeat rewrite_eq.
        rewrite Heq in H0. apply multi_spec_seq_assoc in H0. do 2 destruct H0. apply multi_spec_seq in H0. destruct H0.
        ++ do 8 destruct H0. destruct H3, H4. subst. invert H4. invert H0. invert H16. simpl in H3. rewrite Heq, t_update_same in H3.
           invert H3. invert H0; [inversion H16|]. apply IH in H4; [|prog_size_auto|tauto..]. destruct H4, H0, H3 as (->&?); [reflexivity|].
           pose proof (multi_ideal_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ Harrs H0).
           remember (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_slh P c) end; "b" := be' ? 1 : "b" }}> with (flex_slh P <{{ while be do c end }}>) in H5
            by now simpl; rewrite Heqbe'.
           apply IH in H5; [|prog_size_auto|simpl; tauto..]. do 2 destruct H5.
           eapply multi_ideal_unused_overwrite with (X:="b") (n:=st'0 "b") in H5; [|simpl; tauto]. rewrite t_update_shadow in H5.
           eexists. split; [|intro Hc'; now apply H6, H2]. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { subst. now destruct (label_of_bexp P be); simpl; rewrite ?st_b; destruct b'1. } { reflexivity. }
           rewrite Heq. simpl. eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H0|].
           eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|apply H5].
        ++ do 2 destruct H0. subst. invert H3.
           { eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
           invert H0. invert H15. invert H4.
           { eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. rewrite t_update_shadow, t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
           invert H0; [inversion H15|]. simpl in H3. rewrite Heq, t_update_same in H3. apply IH in H3; [|prog_size_auto|tauto..].
           destruct H3, H0. eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. econstructor; [constructor|].
           econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'1; simpl; rewrite ?st_b. } { reflexivity. }
           rewrite Heq. simpl. apply multi_ideal_add_snd_com, H0.
      * assert (Heq' : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now rewrite <- Heq at 6; destruct (label_of_bexp P be); simpl; destruct (beval st'1 be), (st'1 "b").
        rewrite Heq' in H0. invert H0.
        { eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
        invert H; [inversion H12|]. invert H1.
        { eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
        invert H. invert H0; [|inversion H]. eexists. split; [|split; [reflexivity|now simpl; rewrite Heq'] ].
        rewrite t_update_shadow, t_update_same. econstructor; [constructor|]. econstructor; [econstructor|].
        { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
        simpl. econstructor.
    - destruct (beval st'1 be && (label_of_bexp P be || (st'1 "b" =? 0)%nat)) eqn:Heq.
      * apply andb_prop in Heq. destruct Heq. apply orb_prop in H1.
        assert (Heq : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct H1 as [->|H1], (label_of_bexp P be); simpl; repeat rewrite_eq.
        rewrite Heq in H0. invert H0.
        { eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
        invert H2; [inversion H14|]. invert H3.
        { eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
        invert H0. invert H2; [|inversion H0]. eexists. rewrite t_update_shadow, t_update_same.
        split; [|split; [reflexivity|now simpl; rewrite Heq] ]. rewrite Heq. repeat econstructor; [apply label_of_exp_sound|].
        rewrite <- Heq. now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b.
      * assert (Heq' : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now rewrite <- Heq at 6; destruct (label_of_bexp P be); simpl; destruct (beval st'1 be), (st'1 "b").
        rewrite Heq' in H0. apply multi_spec_seq_assoc in H0. destruct H0, H. apply multi_spec_seq in H. destruct H.
        ++ do 8 destruct H. destruct H1, H2. subst. invert H2. invert H. invert H14. invert H1. invert H; [inversion H14|].
           simpl in H2. rewrite Heq' in H2. apply IH in H2; [|prog_size_auto|tauto..]. destruct H2, H, H1 as (->&?); [reflexivity|].
           rewrite t_update_eq in H. apply multi_ideal_unused_update in H; [|simpl; tauto].
           pose proof (multi_ideal_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ Harrs H).
           remember (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) as be' in H3.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_slh P c) end; "b" := be' ? 1 : "b" }}> with (flex_slh P <{{ while be do c end }}>) in H3
            by now simpl; rewrite Heqbe'.
           apply IH in H3; [|prog_size_auto|simpl; tauto..]. do 2 destruct H3.
           eapply multi_ideal_unused_overwrite with (X:="b") (n:=st'1 "b") in H3; [|simpl; tauto]. rewrite t_update_shadow in H3.
           eexists. split; [|intro Hc'; apply H4, H0, Hc']. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
           eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|]. eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|apply H3].
        ++ do 2 destruct H. subst. invert H1.
           { eexists. split; [|intro Hc'; apply H0 in Hc'; discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
           invert H. invert H13. invert H2.
           { eexists. split; [|intro Hc'; apply H0 in Hc'; discriminate]. rewrite t_update_shadow, t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
           invert H; [inversion H13|]. simpl in H1. rewrite Heq' in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H. rewrite t_update_eq in H. apply multi_ideal_unused_update in H; [|tauto]. eexists.
           split; [|intro Hc'; apply H0 in Hc'; discriminate]. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
           simpl. apply multi_ideal_add_snd_com, H.
  + invert H; [solve_refl|]. invert H0.
    - invert H1; [|inversion H]. eexists. split; [|split; [reflexivity|rewrite t_update_neq; tauto] ].
      rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound| |assumption].
      simpl. now destruct (label_of_aexp P i), (P x), b'; simpl; rewrite ?st_b.
    - destruct (label_of_aexp P i && negb (P x)) eqn:Heq.
      * invert H1; [|inversion H]. eexists. split; [|split; [reflexivity|rewrite t_update_neq; tauto] ].
        rewrite t_update_permute; [|tauto]. rewrite t_update_same. apply andb_prop in Heq. destruct Heq.
        apply negb_true_iff in H0. repeat econstructor; [|tauto..]. unfold public. rewrite <- H. apply label_of_exp_sound.
      * simpl in H14. rewrite st_b in H14. simpl in H14. specialize (Harrs a). lia.
  + invert H; [solve_refl|]. invert H0.
    - invert H1; [|inversion H]. eexists. split; [|tauto]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound..| |assumption].
      now destruct (label_of_aexp P i), (label_of_aexp P e), b'; simpl; rewrite ?st_b.
    - destruct (label_of_aexp P i && label_of_aexp P e) eqn:Heq.
      * invert H1; [|inversion H]. eexists. split; [|tauto]. rewrite t_update_same.
        apply andb_prop in Heq. destruct Heq. fold public in H, H0.
        repeat econstructor; [| |tauto..].
        1: rewrite <- H. 2:rewrite <- H0. all:apply label_of_exp_sound.
      * simpl in H15. rewrite st_b in H15. simpl in H15. specialize (Harrs a). lia.
Qed.

Lemma flex_slh_bcc : forall c ds P st ast (b:bool) c' st' ast' b' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((flex_slh P c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists c'', P |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st', ast', b'))>.
Proof.
  intros. apply flex_slh_bcc_generalized in H2; [|tauto..]. do 2 destruct H2. eexists. apply H2.
Qed.

Lemma gilles_lemma_one_step : forall P c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds,
  pub_equiv P st1 st2 ->
  P |- <((c, st1, ast1, true))> -->i_ds^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i_ds^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2 /\ ct1 = ct2.
Proof.
  intros P c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds. intros Hequiv H.
  remember true as b in H at 1. remember true as bt in H.
  revert st2 ast2 ct2 stt2 astt2 os2 Heqb Heqbt Hequiv. induction H; simpl; intros; subst.
  + now invert H0.
  + invert H0; [|inversion H].
    apply IHideal_eval_small_step in H13; [|tauto..]. destruct H13. now subst.
  + invert H; [inversion H12|tauto].
  + invert H2. eapply bexp_has_label_inj in H; [|eassumption]. subst.
    destruct l; [|tauto]. erewrite noninterferent_bexp; eauto.
  + invert H2. eapply bexp_has_label_inj in H; [|eassumption]. subst.
    destruct l; [|tauto]. erewrite noninterferent_bexp; eauto.
  + now invert H.
  + invert H2. eapply aexp_has_label_inj in H; [|eassumption]. subst.
    destruct li; [|tauto]. erewrite noninterferent_aexp; eauto.
  + invert H4. erewrite noninterferent_aexp; eauto.
  + invert H4. eapply aexp_has_label_inj in H0; [|eassumption]. eapply aexp_has_label_inj in H1; [|eassumption]. subst.
    destruct li; [|tauto]. destruct le0; [|tauto]. erewrite noninterferent_aexp; eauto.
  + invert H5. erewrite noninterferent_aexp; eauto.
Qed.

Lemma gilles_lemma : forall P PA c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds,
  P & PA, public |-- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA ast1 ast2 ->
  P |- <((c, st1, ast1, true))> -->i*_ds^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i*_ds^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2.
Proof.
  intros P PA c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds.
  intros Hwt Hequiv Hequiv' H. remember true as b in H at 1. remember true as bt in H.
  revert st2 ast2 ct2 stt2 astt2 os2 Heqb Heqbt Hwt Hequiv Hequiv'. induction H; intros; subst.
  + apply multi_ideal_obs_length in H. symmetry in H. simpl in H. now apply length_zero_iff_nil in H.
  + pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ H). subst.
    invert H1.
    - symmetry in H5. apply app_eq_nil in H5. destruct H5; subst.
      apply multi_ideal_obs_length in H0. apply ideal_eval_small_step_obs_length in H.
      symmetry in H, H0. apply length_zero_iff_nil in H, H0. now subst.
    - assert (ds0 = ds1).
      { apply app_eq_prefix in H2. apply prefix_eq_length; [|tauto]. eapply ideal_eval_small_step_same_length; eassumption. }
      subst. apply app_inv_head in H2. subst.
      pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ H3). subst.
      pose proof (gilles_lemma_one_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hequiv H H3). destruct H1; subst.
      eapply ideal_eval_small_step_preserves_pub_equiv in Hequiv'; [|eassumption..]. destruct Hequiv'.
      eapply gilles_lemma_one_step in H3; [|eassumption..]. destruct H3; subst.
      eapply ideal_eval_small_step_preserves_wt in Hwt; [|eassumption].
      f_equal. eapply IHmulti_ideal; eauto.
Qed.

Conjecture ideal_eval_relative_secure : forall P c st1 st2 ast1 ast2,
  pub_equiv P st1 st2 ->
  seq_same_obs c st1 st2 ast1 ast2 ->
  ideal_same_obs P c st1 st2 ast1 ast2.

Conjecture flex_slh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_slh P) c st1 st2 ast1 ast2.

