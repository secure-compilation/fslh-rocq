(** * UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import SpecCT.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Relative security *)

(** We would like to also enforce security for arbitrary programs that are do
    not follow the cryptographic constant time programming discipline
    (i.e. which do not satisfy [ct_well_typed]). The goal is to achieve a
    relative notion of security which intuitively ensures that the protected
    program does not leak more information speculatively than the original
    program leaks sequentially via the CT observations. One way to achieve this
    protection is by transforming the program using Ultimate Speculative Load
    Hardening (USLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. *)

(* We need to define [seq_same_obs] wrt a small-step semantics, so that this
   hypothesis also gives us something for sequentially infinite executions. *)

Axiom multi_seq : com -> state -> astate -> com -> state -> astate -> obs -> Prop.

Notation "'<((' c , st , ast '))>' '-->*_(' os ')' '<((' ct , stt , astt '))>'"
  := (multi_seq c st ast ct stt astt os)
       (at level 40, c custom com at level 99, ct custom com at level 99,
           st constr, ast constr, stt constr, astt constr at next level).

Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2 c1 c2,
    <((c, st1, ast1))> -->*_(os1) <((c1, stt1, astt1))> ->
    <((c, st2, ast2))> -->*_(os2) <((c2, stt2, astt2))> ->
    (prefix os1 os2) \/ (prefix os2 os1).

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2 :state) (ast1 ast2 :astate): Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

(** Additional Property on [astaste]'s *)

Definition nonempty_arrs (ast :astate) :Prop :=
  forall a, 0 < length (ast a).

(** * Ultimate Speculative Load Hardening *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(** * Ideal big-step evaluation relation *)

Reserved Notation
         "'|-i' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      |-i <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      |-i <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      |-i <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      |-i <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      |-i <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os2++os1)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, b, ds)> =[ match negb b && beval st be  with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch (negb b && beval st be)])>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, true, ds)> =[ match negb b && beval st be  with
                                 | true => c2 (* <-- branches swapped *)
                                 | false => c1 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch (negb b && beval st be)])>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      |-i <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      |-i <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast (b :bool) x a ie i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_Write : forall st ast (b :bool) a ie i e n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>

  where "|-i <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval c st ast b ds stt astt bb os).

Definition ideal_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

(** * Ideal small-step evaluation relation *)

Reserved Notation
         "'<((' c , st , ast , b '))>' '-->i_(' ds , os ')' '<((' ct , stt , astt , bt '))>'"
         (at level 40, c custom com at level 99, ct custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <((x := e, st, ast, b))> -->i_([],[]) <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      <((c1, st, ast, b))>  -->i_(ds, os) <((c1t, stt, astt, bt))>  ->
      <(((c1;c2), st, ast, b))>  -->i_(ds, os) <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall st ast b c2,
      <(((skip;c2), st, ast, b))>  -->i_([],[]) <((c2, st, ast, b))>
  | ISM_If : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))> -->i_([DStep],[OBranch (negb b && beval st be)])
      <((match negb b && beval st be with
        | true => ct
        | false => cf end, st, ast, b))>
  | ISM_If_F : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))> -->i_([DForce],[OBranch (negb b && beval st be)])
      <((match negb b && beval st be with
        | true => cf
        | false => ct end, st, ast, b))>
  | ISM_While : forall be c st ast b,
      <((while be do c end, st, ast, b))> -->i_([],[])
      <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall x a ie st ast (b :bool) i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast, b))> -->i_([DStep],[OARead a i])
      <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | ISM_Write : forall a ie e st ast (b :bool) i n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast, b))> -->i_([DStep],[OAWrite a i])
      <((skip, st, a !-> upd i (ast a) n; ast, b))>
  
  where "<(( c , st , ast , b ))> -->i_( ds , os )  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step c st ast b ct stt astt bt ds os).

Reserved Notation
         "'<((' c , st , ast , b '))>' '-->i*_(' ds , os ')' '<((' ct , stt , astt , bt '))>'"
         (at level 40, c custom com at level 99, ct custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_refl : <((c, st, ast, b))> -->i*_([],[]) <((c, st, ast, b))>
  | multi_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <((c, st, ast, b))> -->i_(ds1,os1) <((c', st', ast', b'))> ->
      <((c', st', ast', b'))> -->i*_(ds2,os2) <((c'', st'', ast'', b''))> ->
      <((c, st, ast, b))> -->i*_(ds1++ds2,os2++os1) <((c'', st'', ast'', b''))>

  where "<(( c , st , ast , b ))> -->i*_( ds , os )  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal c st ast b ct stt astt bt ds os).

(** * Relative Security of Ultimate Speculative Load Hardening *)

(* HIDE *)
(* Some intuition about Gilles lemma, but now we plan to prove it directly, like determinism *)
Fixpoint observations (c:com) (ds:dirs) : option (obs * dirs) :=
  match c with
  | <{{skip}}> => Some ([],ds)
  | <{{x := e}}> => Some ([],ds)
  | <{{c1; c2}}> =>
      match observations c1 ds with
      | Some (os',ds') =>
          match observations c2 ds' with
          | Some (os'',ds'') => Some (os''++os', ds'')
          | None => None
          end
      | None => None
      end
  | <{{if be then c1 else c2 end}}> =>
      match ds with
      | DStep :: ds' =>
          match observations c2 ds' with
          | Some (os,ds'') => Some (os++[OBranch false],ds'')
          | None => None
          end
      | DForce :: ds' =>
          match observations c1 ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{while be do c end}}> =>
      match ds with
      | DStep :: ds' => Some ([OBranch false],ds')
      | DForce :: ds' =>
          match observations c (* <- should actually be: while be do c end *) ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{x <- a[[i]]}}> => Some ([OARead a 0],ds)
  | <{{a[i] <- e}}> => Some ([OAWrite a 0],ds)
  end.

Lemma observations_fixed : forall c st ast ds stt astt os,
  unused "b" c ->
  st "b" = 1 ->
  |-i <(st, ast, true, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  Some (os,[]) = observations c ds.
Admitted.

Lemma gilles_lemma_follows : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  |-i <(st1, ast1, true, ds)> =[ c ]=> <(stt1, astt1, true, os1)> ->
  |-i <(st2, ast2, true, ds)> =[ c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2 Hunused Hb1 Hb2 H1 H2.
  apply observations_fixed in H1; try auto.
  apply observations_fixed in H2; try auto. congruence.
Qed.
(* /HIDE *)

Lemma gilles_lemma : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  |-i <(st1, ast1, true, ds)> =[ c ]=> <(stt1, astt1, true, os1)> ->
  |-i <(st2, ast2, true, ds)> =[ c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Admitted.

Lemma ideal_unused_update : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)> ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X !-> st X; st', ast', b', os)>.
Proof.
Admitted.

Lemma ideal_unused_update_rev : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X!-> st X; st', ast', b', os)> ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
Admitted.

Lemma spec_eval_preserves_nonempty_arrs : forall c st ast b ds st' ast' b' os,
  nonempty_arrs ast ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  nonempty_arrs ast'.
Admitted.

Lemma flag_zero_check_spec_bit : forall (st :state) (X :string) (b b' :bool), 
  st X = (if b then 1 else 0) ->
  (st X =? 0)%nat = b' ->
  b = negb b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.

Lemma flag_one_check_spec_bit : forall (st :state) (X :string) (b b' :bool), 
  st X = (if b then 1 else 0) ->
  (st X =? 1)%nat = b' ->
  b = b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.


Definition ultimate_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall st ast (b:bool) st' ast' (b':bool) os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
  st' "b" = (if b' then 1 else 0).

Lemma ultimate_slh_flag : forall c ds,
  ultimate_slh_flag_prop c ds.
Admitted.

Definition ultimate_slh_bcc_prop (c: com) (ds :dirs) :Prop :=
  forall st ast (b: bool) st' ast' b' os,
    nonempty_arrs ast ->
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
    |-i <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

(* LATER: Prove the used lemmas [ultimate_slh_flag], [ideal_unused_update_rev],
   [spec_eval_preserves_nonempty_arrs] and [ideal_unused_update] *)
Lemma ultimate_slh_bcc : forall c ds,
  ultimate_slh_bcc_prop c ds.
Proof.
  apply prog_size_ind. unfold ultimate_slh_bcc_prop.
  intros c ds IH st ast b st' ast' b' os Hast Hunused Hstb Heval.
  destruct c; simpl in *; inversion Heval; subst; clear Heval.
  - (* Skip *)
    rewrite t_update_same. apply Ideal_Skip.
  - (* Asgn *) 
    rewrite t_update_permute; [| tauto].
    rewrite t_update_same.
    constructor. reflexivity.
  - (* Seq *) 
    eapply Ideal_Seq.
    + apply IH in H1; try tauto.
      * eassumption.
      * prog_size_auto.
    + apply ultimate_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * prog_size_auto.
      * eapply spec_eval_preserves_nonempty_arrs in H1; auto. 
  (* IF *)
  - (* non-speculative *)
    simpl in *. destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
    + (* true *)
      destruct (beval st be) eqn:Eqbe; simpl in H10; 
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *;
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.  
      * replace (OBranch true) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
        apply Ideal_If. rewrite app_nil_r. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto. prog_size_auto.
      * replace (OBranch false) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
        apply Ideal_If. rewrite app_nil_r. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto. prog_size_auto.
    + (* false *)
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *.
      rewrite Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit. 
      replace (OBranch false) with (OBranch (negb b'0 && beval st be))
        by (rewrite Hbit; reflexivity). 
      apply Ideal_If. rewrite app_nil_r. subst; simpl.
      apply IH in H11; try tauto. prog_size_auto.
  - (* speculative *)
    simpl in *. destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
    + (* true *)
      destruct (beval st be) eqn:Eqbe; simpl in H10; 
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *;
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.  
      * replace (OBranch true) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11. 
        apply Ideal_If_F. rewrite app_nil_r. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto.
        { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
        { prog_size_auto. }
      * replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11.
        apply Ideal_If_F. rewrite app_nil_r. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto.
        { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
        { prog_size_auto. }
    + (* false *)
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *.
      rewrite Eqstb in H11; simpl in H11. 
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit. 
      replace (OBranch false) with (OBranch (negb b && beval st be))
        by (rewrite Hbit; reflexivity). 
      apply Ideal_If_F. rewrite app_nil_r. subst; simpl.
      apply IH in H11; try tauto.
      { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
      { prog_size_auto. }
  - (* While *) 
    eapply Ideal_While.
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11; simpl in *.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl. rewrite app_nil_r.
      destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
      * destruct (beval st be) eqn:Eqbe;
        inversion H12; subst; clear H12.
        { assert(Hwhile: <(st'1, ast'1, b'1, ds2)> 
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
            replace os2 with ([] ++ os2)%list by reflexivity.
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch true) with (OBranch (negb b && beval st be))
            by (rewrite Eqbe, Hbit; reflexivity).
          apply Ideal_If. rewrite Eqbe; subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite app_nil_r. rewrite Eqbe, Eqstb in H11; simpl in H11. 
            rewrite t_update_same in H11. apply IH in H11; try tauto.
            prog_size_auto.
          - apply IH in Hwhile; try tauto.
            + eapply ideal_unused_update_rev; eauto.
            + prog_size_auto.
            + eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            + auto.
            + inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
              apply ultimate_slh_flag in H11; try tauto. }
        { eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b'0 && beval st'0 be))
            by (rewrite Hbit, Eqbe; reflexivity).
          apply Ideal_If. rewrite Eqbe; subst; simpl.
          inversion H10; subst; clear H10; simpl in *. rewrite Eqbe, Eqstb; simpl.
          rewrite t_update_shadow. rewrite t_update_same. apply Ideal_Skip. }
      * eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
        replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Hbit; reflexivity).
        apply Ideal_If. subst; simpl.  
        inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqstb; simpl. rewrite t_update_shadow. rewrite t_update_same.
        apply Ideal_Skip.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl. rewrite app_nil_r.
      destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
      * destruct (beval st be) eqn:Eqbe;
        inversion H12; subst; clear H12.
        { eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch true) with (OBranch (negb b && beval st'0 be))
            by (rewrite Hbit, Eqbe; reflexivity).
          apply Ideal_If_F. rewrite Eqbe; subst; simpl.  
          inversion H10; subst; clear H10; simpl in *.
          rewrite Eqstb; simpl. rewrite t_update_shadow. rewrite t_update_same.
          apply Ideal_Skip. }
        { assert(Hwhile: <(st'1, ast'1, b'1, ds2)> 
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
            replace os2 with ([] ++ os2)%list by reflexivity.
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b && beval st be))
            by (rewrite Eqbe, Hbit; reflexivity).
          apply Ideal_If_F. rewrite Eqbe; subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite app_nil_r. rewrite Eqbe, Eqstb in H11; simpl in H11.
            apply IH in H11; try tauto.
            + eapply ideal_unused_update in H11; try tauto. 
            + prog_size_auto.
          - apply IH in Hwhile; try tauto.
            + eapply ideal_unused_update_rev; eauto.
            + prog_size_auto.
            + eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            + auto.
            + inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqbe, Eqstb in H11; simpl in H11. 
              apply ultimate_slh_flag in H11; try tauto. }
      * inversion H12; subst; clear H12.
        assert(Hwhile: <(st'1, ast'1, b'1, ds2)> 
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
            replace os2 with ([] ++ os2)%list by reflexivity.
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b && beval st be))
            by (rewrite Hbit; reflexivity).
          apply Ideal_If_F. subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          { inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite app_nil_r. rewrite Eqstb in H11; simpl in H11. 
            apply IH in H11; try tauto.
            - rewrite t_update_eq in H11.
              eapply ideal_unused_update in H11; try tauto. 
            -  prog_size_auto. }
          { apply IH in Hwhile; try tauto.
            - eapply ideal_unused_update_rev; eauto.
            - prog_size_auto.
            - eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            - auto.
            - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqstb in H11; simpl in H11.
              apply ultimate_slh_flag in H11; try tauto. }
  - (* ARead *)
    simpl in H11. destruct (st "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
  - (* ARead; contradiction *) simpl in H11. rewrite Hstb in H11; simpl in H11.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H11.
    exfalso; auto.
  - (* AWrite *)
    simpl in H12. destruct (st' "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
  - (* AWrite; contradiction *) simpl in H12. rewrite Hstb in H12; simpl in H12.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H12.
    exfalso; auto.
Qed.

Conjecture ideal_eval_bit_deterministic : 
  forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, b, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, b, ds)> =[ c ]=> <(stt2, astt2, bt2, os2 )> ->
    bt1 = bt2.

Conjecture ideal_eval_final_bit_false : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, false, os)> ->
  (forall d, In d ds -> d = DStep).

Conjecture ideal_eval_no_spec : forall c st ast ds stt astt bt os,
  (forall d, In d ds -> d = DStep) ->
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  <((c, st, ast ))> -->*_(os) <((skip, stt, astt))>.

Conjecture ideal_prefix_dirs : 
  forall c st1 st2 ast1 ast2 b1 b2 ds1 ds2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
  prefix ds1 ds2 ->
  |-i <(st1, ast1, b1, ds1)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
  |-i <(st2, ast2, b2, ds2)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
  ds1 = ds2.

Lemma ideal_spec_needs_force : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  b = false ->
  bt = true ->
  In DForce ds.
Proof.
  intros c st ast b ds stt astt bt os Heval Hb Hbt.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Lemma ideal_eval_dirs : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  (forall d, In d ds -> d = DStep \/ d = DForce).
Proof.
  intros c sst ast b ds stt astt bt os Hev.
  induction Hev; intros d Hin; simpl in Hin; try (now destruct Hin; auto).
  - apply in_app_or in Hin as [Hds1 | Hds2]; auto.
  - apply IHHev; auto.
Qed.

Lemma ideal_dirs_split : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  b = false ->
  bt = true ->
  exists ds1 ds2, (forall d, In d ds1 -> d = DStep) /\ ds1 ++ (DForce::ds2) = ds
  (* /\ exists c' st' ast' c'' st'' ast'' os1 os2 os', *)
  (*   os2 ++ (os' ++ os1) = os /\ *)
  (*   <((c, st, ast, b))> -->i*_(ds1,os1) <((c', st', ast', b))> /\ *)
  (*   <((c', st', ast', b))>  -->i_([DForce],os') <((c'', st'', ast'', true))> /\ *)
  (*   |-i <(st'', ast'', true, ds2)> =[ c'' ]=> <(stt, astt, bt, os2)> *).
Proof.
  intros c st ast b ds stt astt bt os Hev Hb Hbt.
  induction Hev; subst; simpl; eauto; try discriminate.
  - destruct b' eqn:Eqb'.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev1 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists ds3; exists (ds4 ++ ds2). split; auto.
      rewrite app_comm_cons. rewrite app_assoc. rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev2 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (ds1 ++ ds3); exists ds4. split.
      * intros d H. apply in_app_or in H as [Hds1 | Hds3]; auto.
        eapply ideal_eval_final_bit_false in Hev1; [| eapply Hds1]. auto.
      * rewrite <- app_assoc. rewrite Heq. reflexivity.
  - (* IF non-speculative *)
    simpl in Hev. destruct (beval st be) eqn:Eqbe.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * rewrite Heq. reflexivity.
  - (* IF speculative *)
    exists []; exists ds. split; simpl.
    + intros d H; destruct H.
    + reflexivity.
Qed.


Lemma ideal_relative_secure : forall c st1 st2 ast1 ast2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  ideal_same_obs c st1 st2 ast1 ast2.
Proof.
  unfold ideal_same_obs. intros c st1 st2 ast1 ast2 Hsec 
  ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  eapply ideal_eval_bit_deterministic in Hev1 as SameB; try eassumption. subst.
  destruct bt1 eqn:Eqbt1.
  - (* with speculation *)
    destruct c as [| X e | c1 c2 | be ct cf | be cw | X a ie | a ie e ] eqn:Eqnc;
    try (now inversion Hev1).
    + (* Seq *)
      inversion Hev1; subst; clear Hev1; inversion Hev2; subst; clear Hev2.
      assert (Hdirs: ds0 = ds1 /\ ds3 = ds2).
      { assert (L: prefix (ds0 ++ ds3) (ds1++ds2)) by (rewrite H2; apply prefix_refl).
        apply prefix_app in L. destruct L as [Hdir | Hdir].
        - eapply ideal_prefix_dirs in H1; eauto. subst.
          apply app_inv_head_iff in H2. subst. auto.
        - eapply ideal_prefix_dirs in H6; eauto. subst.
          apply app_inv_head_iff in H2. subst. auto. }
      destruct Hdirs; subst.
      eapply ideal_eval_bit_deterministic in H1 as SameB; try eassumption. subst.
      destruct b' eqn:Eqb'.
      (* HIDE: Analog cases to the destruct of bt1. Therefore same issues with using
         <(_, _, false, _)> =[c]=> <(_, _, true, _)> . *)
      * admit.
      * admit.
    + (* If *)
      inversion Hev1; subst; clear Hev1; inversion Hev2; subst; clear Hev2.
      * destruct (beval st1 be) eqn:Eqst1be; destruct (beval st2 be) eqn:Eqst2be; simpl in *.
        { (* HIDE: Hard to relate ideal to sequential execution. But without relating, how
             to use seq_obs_sec. *) admit. }
        { admit. }
        { admit. }
        { admit. }
      * admit.
    + (* While *) admit. 
  - (* without speculation *)
    assert (Hds: forall d, In d ds -> d = DStep).
    { intros; eapply ideal_eval_final_bit_false in Hev1; eauto. }
    eapply ideal_eval_no_spec in Hev1; try assumption.
    eapply ideal_eval_no_spec in Hev2; try assumption.
    eauto. admit. (* <- This fails after change to seq_same_obs
                   Need to additionally show that |ds| = |os1| = |os2| *)
Admitted.

Theorem ultimate_slh_relative_secure :
  forall c st1 st2 ast1 ast2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    (* extra assumptions on astates *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure ultimate_slh c st1 st2 ast1 ast2.
Proof. (* from bcc + ideal_relative_secure *)
  unfold relative_secure.
  intros c st1 st2 ast1 ast2 Hunused Hst1b Hst2b Hast1 Hast2 Hseq ds stt1 stt2 
    astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  apply ultimate_slh_bcc in Hev1; try assumption.
  apply ultimate_slh_bcc in Hev2; try assumption.
  eapply (ideal_relative_secure c st1 st2); eassumption.
Qed.

(* HIDE *)
(* CH: Some playing with BCC generalization *)

Definition ct_preservation trans : Prop := forall c,
  (forall st1 st2 ast1 ast2, ideal_same_obs c st1 st2 ast1 ast2) ->
  (forall st1 st2 ast1 ast2, spec_same_obs (trans c) st1 st2 ast1 ast2).

Definition secure_compilation_bw trans :=
  forall c, exists Td To, forall ds st ast ost st' ast' b,
      <(st, ast, false, ds)> =[trans c]=> <(st', ast', b, ost)> ->
     exists oss,
      |-i <(st, ast, false, Td ds)> =[c]=> <(st', ast', b, oss)> /\
      ost = To oss.

(* Theorem 2 of Santiago's POPL submission *)
Theorem ct_preservation_bw : forall trans,
  secure_compilation_bw trans ->
  ct_preservation trans.
Proof.
  unfold secure_compilation_bw, ct_preservation, ideal_same_obs, spec_same_obs.
  intros trans H c Hsrc st1 st2 ast1 ast2
         ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 H1 H2.
  specialize (H c). destruct H as [Td [To H] ].
  apply H in H1. destruct H1 as [oss1 [H1 H1'] ].
  apply H in H2. destruct H2 as [oss2 [H2 H2'] ].
  subst. f_equal. eapply Hsrc; eassumption.
Qed.

(* The same proof also applies in our setting to prove relative security from
   speculative source semantics (our ideal semantics) to speculative target
   semantics for the transformed program. In fact this is very similar to
   our use of BCC, just that in our setting both Td and To are identity. *)
Theorem relative_secure_bw : forall trans,
  secure_compilation_bw trans ->
  forall c st1 st2 ast1 ast2,
    ideal_same_obs c st1 st2 ast1 ast2 ->
    spec_same_obs (trans c) st1 st2 ast1 ast2.
Proof.
  unfold secure_compilation_bw, relative_secure, ideal_same_obs, spec_same_obs.
  intros trans H c st1 st2 ast1 ast2 Hsrc
         ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 H1 H2.
  specialize (H c). destruct H as [Td [To H] ].
  apply H in H1. destruct H1 as [oss1 [H1 H1'] ].
  apply H in H2. destruct H2 as [oss2 [H2 H2'] ].
  subst. f_equal. eapply Hsrc; eassumption.
Qed.
(* /HIDE *)
