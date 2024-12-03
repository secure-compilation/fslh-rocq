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

Scheme aexp_bexp_ind := Induction for aexp Sort Prop
  with bexp_aexp_ind := Induction for bexp Sort Prop.

Ltac rewrite_eq :=
  match goal with
  | H:_=_ |- _ => rewrite H; clear H
  | H:forall _, _=_ |- _ => rewrite H; clear H
  | _ => idtac
 end.

Ltac invert H := inversion H; subst; clear H.

Definition label_of_aexp (P:pub_vars) (a:aexp) : label :=
  List.fold_left (fun l a => join l (P a)) (vars_aexp a) public.

Definition label_of_bexp (P:pub_vars) (b:bexp) : label :=
  List.fold_left (fun l b => join l (P b)) (vars_bexp b) public.

Definition is_empty {A : Type} (l : list A) := match l with [] => true | _ => false end.

Lemma is_empty_true {A} (l : list A) :
  is_empty l = true -> l = [].
Proof. now destruct l. Qed.

Lemma no_vars_public_bexp : forall P b,
  is_empty (vars_bexp b) = true ->
  label_of_bexp P b = public.
Proof. intros P b H. apply is_empty_true in H. unfold label_of_bexp. now rewrite_eq. Qed.

Lemma no_vars_public_aexp : forall P a,
  is_empty (vars_aexp a) = true ->
  label_of_aexp P a = public.
Proof. intros P a H. apply is_empty_true in H. unfold label_of_aexp. now rewrite_eq. Qed.

Definition AllPub : pub_vars := (_!-> public).
Definition AllSecret : pub_vars := (_!-> secret).

Lemma joining_to_secret : forall l' (xs:list string),
  List.fold_left (fun l b => join l l') xs secret = secret.
Proof. intros P xs. induction xs; eauto. Qed.

Lemma all_secret_bexp : forall b,
  is_empty (vars_bexp b) = false ->
  label_of_bexp AllSecret b = secret.
Proof.
  intros b H. unfold label_of_bexp. destruct (vars_bexp b) eqn:Eq; [discriminate|rewrite_eq].
  unfold AllSecret, t_empty. simpl. apply joining_to_secret.
Qed.

Lemma all_secret_aexp : forall a,
  is_empty (vars_aexp a) = false ->
  label_of_aexp AllSecret a = secret.
Proof.
  intros a H. unfold label_of_aexp. destruct (vars_aexp a) eqn:Eq; [discriminate|rewrite_eq].
  unfold AllSecret, t_empty. simpl. apply joining_to_secret.
Qed.

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
    if label_of_aexp P i
    then (* Selective SLH -- mask the value of public loads *)
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
                   else <{{x <- a[[i]]}}>
    else (* Ultimate SLH -- mask private address of load *)
      <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> =>
    let i' := if label_of_aexp P i
      then i (* Selective SLH -- no mask even if it's out of bounds! *)
      else <{{("b" = 1) ? 0 : i}}> (* Ultimate SLH *)
    in <{{a[i'] <- e}}> (* <- Doing nothing here in label_of_aexp P i = true case okay for Spectre v1,
                              but would be problematic for return address or code pointer overwrites *)
  end)%string.

(* For CT programs this is the same as sel_slh *)

Module RelatingSelSLH.

  Lemma label_of_aexp_sound : forall P a,
    P |-a- a \in label_of_aexp P a.
  Admitted.

  Lemma label_of_aexp_unique : forall P a l,
    P |-a- a \in l ->
    l = label_of_aexp P a.
  Admitted.

  Lemma label_of_bexp_sound : forall P b,
    P |-b- b \in label_of_bexp P b.
  Admitted.

  Lemma label_of_bexp_unique : forall P b l,
    P |-b- b \in l ->
    l = label_of_bexp P b.
  Admitted.

  Lemma sel_slh_is_flex_slh : forall P PA c,
      ct_well_typed P PA c ->
      sel_slh P c = flex_slh P c.
  Proof.
    intros P PA c H. induction H; simpl; repeat rewrite_eq; try reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
  Qed.

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
  | ISM_If : forall P be ct cf st ast b c' b',
      b' = (label_of_bexp P be || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | ISM_If_F : forall P be ct cf st ast b c' b',
      b' = (label_of_bexp P be || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | ISM_While : forall P be c st ast b,
      P |- <((while be do c end, st, ast, b))> -->i_[]^^[]
            <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall P x a ie st ast (b :bool) i,
      (if negb (label_of_aexp P ie) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
            <((skip, x !-> (if label_of_aexp P ie && P x && b then 0 else nth i (ast a) 0); st, ast, b))>
  | ISM_ARead_U : forall P x a ie st ast i a' i',
      aeval st ie = i ->
      label_of_aexp P ie = public ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i]
            <((skip, x !-> (if P x then 0 else nth i' (ast a') 0); st, ast, true))>
  | ISM_Write : forall P a ie e st ast (b :bool) i n,
      aeval st e = n ->
      (if negb (label_of_aexp P ie) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      P |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
            <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | ISM_Write_U : forall P a ie e st ast i n a' i',
      aeval st e = n ->
      label_of_aexp P ie = public ->
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

Definition ideal_same_obs P c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((c1, stt1, astt1, bt1))> ->
    P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((c2, stt2, astt2, bt2))> ->
    os1 = os2.

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
  + invert H. { eexists. rewrite t_update_same. now repeat constructor. } invert H0.
  + invert H. { eexists. rewrite t_update_same. now repeat constructor. } invert H0. invert H1; [|inversion H]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
    eexists. repeat econstructor. rewrite t_update_neq; tauto.
  + apply multi_spec_seq in H. admit.
  + admit.
  + admit.
  + admit.
  + admit.
  (*
    invert H. { eexists. rewrite t_update_same. constructor. }
    destruct (label_of_aexp P i) eqn:Hlbl.
    - destruct (P x) eqn:HPx.
      * invert H0. invert H12.
        { invert H1; [admit|]. invert H; [inversion H12|]. invert H0; [admit|]. invert H. invert H1; [|inversion H].
          rewrite t_update_shadow, t_update_permute; [|tauto]. rewrite t_update_same. exists Skip. rewrite !app_nil_l. repeat econstructor; [now rewrite Hlbl|tauto|].
          simpl. rewrite HPx, t_update_neq; [|tauto]. rewrite st_b, t_update_eq, Hlbl. destruct b'; simpl; constructor. }
        invert H1; [admit|]. invert H; [inversion H12|]. invert H0; [admit|]. invert H. invert H1; [|inversion H]. rewrite t_update_shadow, t_update_permute; [|tauto].
        rewrite t_update_same. eexists. econstructor; [constructor; tauto|]. simpl. rewrite HPx, t_update_neq; [|tauto]. rewrite st_b, t_update_eq. simpl. constructor.
      * invert H0.
        { invert H1; [|inversion H]. repeat econstructor; [now rewrite Hlbl|tauto|]. rewrite t_update_permute; [|tauto]. rewrite t_update_same, HPx, andb_false_r. constructor. }
        invert H1; [|inversion H]. rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor; [tauto..|]. rewrite HPx. constructor.
    - invert H0.
      { invert H1; [|inversion H]. rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor; [now rewrite Hlbl; simpl; destruct b'; rewrite st_b|tauto|].
        simpl. rewrite st_b, Hlbl. destruct b'; simpl; constructor. }
      invert H1; [|inversion H]. simpl in *. rewrite st_b in H14. specialize (Harrs a). simpl in *. lia.
  + invert H. { eexists. rewrite t_update_same. constructor. }
    destruct (label_of_aexp P i) eqn:Hlbl; invert H0; (invert H1; [|inversion H]); rewrite t_update_same; repeat econstructor; try tauto.
    - now rewrite Hlbl.
    - simpl. rewrite Hlbl, st_b. now destruct b'.
    - simpl in H15. rewrite st_b in H15. specialize (Harrs a). simpl in H15. lia.
    - simpl in H15. rewrite st_b in H15. specialize (Harrs a). simpl in H15. lia.
  *)
Admitted.

Lemma flex_slh_bcc : forall c ds P st ast (b:bool) c' st' ast' b' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((flex_slh P c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists c'', P |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st', ast', b'))>.
Admitted.

Conjecture gilles_lemma : forall P c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds,
  pub_equiv P st1 st2 ->
  P |- <((c, st1, ast1, true))> -->i*_ds^^os2 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i*_ds^^os1 <((ct2, stt2, astt2, true))> ->
  os1 = os2.

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

