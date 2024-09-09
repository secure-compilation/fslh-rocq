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

(** We would like to also enforce security for arbitrary programs that do
    not follow the cryptographic constant time programming discipline
    (i.e. which do not satisfy [ct_well_typed]). The goal is to achieve a
    relative notion of security which intuitively ensures that the protected
    program does not leak more information speculatively than the original
    program leaks sequentially via the CT observations. One way to achieve this
    protection is by transforming the program using Ultimate Speculative Load
    Hardening (USLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. *)

(** We need to define [seq_same_obs] below wrt a small-step semantics, so that
    this hypothesis also gives us something for sequentially infinite
    executions, and also for executions that sequentially get stuck because of
    out of bound accesses. *)

(** Sequential small-step semantics *)

Reserved Notation
  "'<((' c , st , ast '))>' '-->^' os '<((' ct , stt , astt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive seq_eval_small_step :
    com -> state -> astate ->
    com -> state -> astate -> obs -> Prop :=
  | SSM_Asgn  : forall st ast e n x,
      aeval st e = n ->
      <((x := e, st, ast))> -->^[] <((skip, x !-> n; st, ast))>
  | SSM_Seq : forall c1 st ast os c1t stt astt c2,
      <((c1, st, ast))>  -->^os <((c1t, stt, astt))>  ->
      <(((c1;c2), st, ast))>  -->^os <(((c1t;c2), stt, astt))>
  | SSM_Seq_Skip : forall st ast c2,
      <(((skip;c2), st, ast))>  -->^[] <((c2, st, ast))>
  | SSM_If : forall be ct cf st ast,
      <((if be then ct else cf end, st, ast))> -->^[OBranch (beval st be)]
      <((match beval st be with
        | true => ct
        | false => cf end, st, ast))>
  | SSM_While : forall be c st ast,
      <((while be do c end, st, ast))> -->^[]
      <((if be then c; while be do c end else skip end, st, ast))>
  | SSM_ARead : forall x a ie st ast i,
      aeval st ie = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast))> -->^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast))>
  | SSM_Write : forall a ie e st ast i n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast))> -->^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast))>

  where "<(( c , st , ast ))> -->^ os  <(( ct ,  stt , astt ))>" :=
    (seq_eval_small_step c st ast ct stt astt os).

Reserved Notation
   "'<((' c , st , ast '))>' '-->*^' os '<((' ct , stt , astt '))>'"
   (at level 40, c custom com at level 99, ct custom com at level 99,
    st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_seq (c:com) (st:state) (ast:astate) :
    com -> state -> astate -> obs -> Prop :=
  | multi_seq_refl : <((c, st, ast))> -->*^[] <((c, st, ast))>
  | multi_seq_trans (c':com) (st':state) (ast':astate)
                (c'':com) (st'':state) (ast'':astate)
                (os1 os2 : obs) :
      <((c, st, ast))> -->^os1 <((c', st', ast'))> ->
      <((c', st', ast'))> -->*^os2 <((c'', st'', ast''))> ->
      <((c, st, ast))> -->*^(os2++os1) <((c'', st'', ast''))>

  where "<(( c , st , ast ))> -->*^ os <(( ct ,  stt , astt ))>" :=
    (multi_seq c st ast ct stt astt os).

Lemma seq_big_to_small_step : forall c st ast stt astt os,
  <(st, ast)> =[ c ]=> <(stt, astt, os)> ->
  <((c, st, ast))> -->*^os <((skip, stt, astt))>.
Proof.
Admitted.

Lemma seq_small_to_big_step : forall c st ast stt astt os,
  <((c, st, ast))> -->*^os <((skip, stt, astt))> ->
  <(st, ast)> =[ c ]=> <(stt, astt, os)>.
Proof.
Admitted.


(** * Defintion of Relative Secure *)

Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2 c1 c2,
    <((c, st1, ast1))> -->*^os1 <((c1, stt1, astt1))> ->
    <((c, st2, ast2))> -->*^os2 <((c2, stt2, astt2))> ->
    (prefix os1 os2) \/ (prefix os2 os1).

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com)
    (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

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
  | <{{x <- a[[i]]}}> => <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(** The masking USLH does for indices requires that our arrays are nonempty. *)

Definition nonempty_arrs (ast : astate) :Prop :=
  forall a, 0 < length (ast a).

(** * Ideal big-step evaluation *)

(** As in SpecCT, we define an ideal big-step evaluation relation, which
    abstractly captures the masking done by USLH. *)

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

(** * Ideal small-step evaluation *)

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall st ast b c2,
      <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))>
      -->i_[DStep]^^[OBranch (negb b && beval st be)]
      <((match negb b && beval st be with
        | true => ct
        | false => cf end, st, ast, b))>
  | ISM_If_F : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))>
      -->i_[DForce]^^[OBranch (negb b && beval st be)]
      <((match negb b && beval st be with
        | true => cf
        | false => ct end, st, ast, true))>
  | ISM_While : forall be c st ast b,
      <((while be do c end, st, ast, b))> -->i_[]^^[]
      <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall x a ie st ast (b :bool) i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | ISM_Write : forall a ie e st ast (b :bool) i n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast, b))>

  where "<(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step c st ast b ct stt astt bt ds os).

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      <((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      <((c, st, ast, b))> -->i*_(ds1++ds2)^^(os2++os1) <((c'', st'', ast'', b''))>

  where "<(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal c st ast b ct stt astt bt ds os).

Lemma ideal_big_to_small_step : forall c st ast b stt astt bt ds os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  <((c, st, ast, b))> -->i*_ds^^os <((skip, stt, astt, bt))>.
Proof.
  intros c st ast b stt astt bt ds os Hbig. induction Hbig.
  - (* Skip *) apply multi_ideal_refl.
  - (* Asgn*)
    replace ([] :dirs) with ([]++[] :dirs) by (apply app_nil_r).
    replace ([] :obs) with ([]++[] :obs) by (apply app_nil_r).
    eapply multi_ideal_trans.
    + eapply ISM_Asgn. eapply H.
    + apply multi_ideal_refl.
  - (* Seq *) admit.
  - (* IF *)
    replace (DStep:: ds) with ([DStep] ++ ds) by reflexivity.
    eapply multi_ideal_trans.
    + apply ISM_If.
    + apply IHHbig.
  - (* IF_F *)
    replace (DForce:: ds) with ([DForce] ++ ds) by reflexivity.
    eapply multi_ideal_trans.
    + apply ISM_If_F.
    + apply IHHbig.
  - (* While *)
    replace (ds) with ([]++ds) by reflexivity.
    replace (os) with (os++[]) by (apply app_nil_r).
    eapply multi_ideal_trans.
    + eapply ISM_While.
    + apply IHHbig.
  - (* ARead *)
    replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
    replace ([OARead a i]) with ([]++[OARead a i]) by (apply app_nil_l).
    eapply multi_ideal_trans.
    + eapply ISM_ARead; auto.
    + apply multi_ideal_refl.
  - (* AWrite *)
    replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
    replace ([OAWrite a i]) with ([]++[OAWrite a i]) by (apply app_nil_l).
    eapply multi_ideal_trans.
    + eapply ISM_Write; auto.
    + rewrite H. apply multi_ideal_refl.
Admitted.

Lemma ideal_eval_one_step : forall c1 c2 st stm stt ast astm astt b bm bt ds1 ds2 os1 os2,
  <((c1, st, ast, b))> -->i_ds1^^os1 <((c2, stm, astm, bm))> ->
  |-i <(stm, astm, bm, ds2)> =[ c2 ]=> <(stt, astt, bt, os2)> ->
  |-i <(st, ast, b, ds1++ds2)> =[ c1 ]=> <(stt, astt, bt, os2++os1)>.
Proof.
  intros c1 c2 st stm stt ast astm astt b bm bt ds1 ds2 os1 os2 Hsmall.
  generalize dependent os2; generalize dependent ds2;
  generalize dependent bt; generalize dependent astt;
  generalize dependent stt.
  induction Hsmall; intros stt' astt' bt' ds2 os2 Hbig.
  - (* ISM_Asgn *)
    inversion Hbig; subst; simpl in *. apply Ideal_Asgn; auto.
  - (* ISM_Seq *)
    inversion Hbig; subst; simpl in *. apply IHHsmall in H1.
    replace (ds ++ ds1 ++ ds0) with ((ds ++ ds1) ++ ds0) by (rewrite app_assoc; auto).
    replace ((os0 ++ os1) ++ os) with (os0 ++ os1 ++ os) by (rewrite app_assoc; auto).
    eapply Ideal_Seq; eauto.
  - (* ISM_Seq_Skip *)
    eapply Ideal_Seq; eauto. apply Ideal_Skip.
  - (* ISM_If *)
    apply Ideal_If; auto.
  - (* ISM_If_F *)
    apply Ideal_If_F; auto.
  - (* ISM_While *)
    rewrite app_nil_l; rewrite app_nil_r. apply Ideal_While. apply Hbig.
  - (* ISM_ARead *)
    inversion Hbig; subst; simpl in *. apply Ideal_ARead; auto.
  - (* ISM_Write *)
  inversion Hbig; subst; simpl in *. apply Ideal_Write; auto.
Qed.

Lemma ideal_small_to_big_step : forall c st ast b stt astt bt ds os,
  <((c, st, ast, b))> -->i*_ds^^os <((skip, stt, astt, bt))> ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)>.
Proof.
  intros c st ast b stt astt bt ds os Hsmall.
  remember <{{skip}}> as ct eqn:Eqct. induction Hsmall; subst.
  - apply Ideal_Skip.
  - assert (L: <{{ skip }}> = <{{ skip }}>) by reflexivity.
    apply IHHsmall in L. eapply ideal_eval_one_step; eauto.
Qed.

(** * Relative Security of Ultimate Speculative Load Hardening *)

(* HIDE *)
(* Some intuition about Gilles lemma 1 from the USLH paper,
   but now we plan to prove it directly, like determinism (see below) *)

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
          (* `c` below should actually be `while be do c end`,
              but then termination no longer obvious  *)
          match observations c ds' with
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
  |-i <(st1, ast1, true, ds)> =[ c ]=> <(stt1, astt1, true, os1)> ->
  |-i <(st2, ast2, true, ds)> =[ c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Admitted.

(** As in SpecCT and Spectre Declassified, an important step in the proof is
    relating the speculative semantics of the hardened program with the ideal
    semantics, by means of a backwards compiler correctness (BCC) result. *)

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

(* LATER: Prove the used lemmas [ultimate_slh_flag], [ideal_unused_update_rev],
   [spec_eval_preserves_nonempty_arrs] and [ideal_unused_update] *)

Definition ultimate_slh_bcc_prop (c: com) (ds :dirs) :Prop :=
  forall st ast (b: bool) st' ast' b' os,
    nonempty_arrs ast ->
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
    |-i <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

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

Lemma ideal_spec_needs_force : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  In DForce ds.
Proof.
  intros c st ast ds stt astt os Heval.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
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

Lemma ideal_obs_length : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  length ds = length os.
Proof.
  intros c st ast b ds stt astt bt os Hev. induction Hev; simpl; auto.
  - do 2 rewrite app_length. lia.
  - rewrite app_length; simpl. lia.
  - rewrite app_length; simpl. lia.
Qed.

Lemma prefix_eq_length : forall {X:Type} (ds1 ds2 : list X),
  length ds1 = length ds2 ->
  prefix ds1 ds2 \/ prefix ds2 ds1 ->
  ds1 = ds2.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 Hlen Hpre; simpl in *.
  - symmetry in Hlen. apply length_zero_iff_nil in Hlen. auto.
  - destruct ds2 as [| d2 ds2'] eqn:Eqds2; simpl in *.
    + discriminate Hlen.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads_and_tails in Hpre as [Heq Hpre];
      subst; inversion Hlen; apply IH in H0; auto; subst; reflexivity.
Qed.

Lemma prefix_app_end : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix ds2 ds3 \/ prefix ds3 ds2 ->
  prefix (ds1 ++ ds2) (ds1 ++ ds3) \/ prefix (ds1 ++ ds3) (ds1 ++ ds2).
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H; simpl.
  - auto.
  - apply IH in H. destruct H as [H | H]; [left | right];
    apply prefix_cons; apply H.
Qed.

Lemma ideal_spec_bit_monotonic : forall c st ast ds stt astt bt os,
  |-i <(st, ast, true, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  bt = true.
Proof.
  intros c st ast ds stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto.
Qed.

Lemma ideal_eval_final_bit_false : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, false, os)> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros c st ast ds stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; intros d Hin; subst; simpl in *; try (now destruct Hin; auto); auto.
  - (* Seq *)
    destruct b' eqn:Eqb'.
    + apply ideal_spec_bit_monotonic in Hev2. discriminate Hev2.
    + apply in_app_or in Hin as [Hds1 | Hds2].
      * apply IHHev1; auto.
      * apply IHHev2; auto.
  - apply ideal_spec_bit_monotonic in Hev. discriminate Hev.
Qed.

Lemma ideal_dirs_split : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  exists ds1 ds2, (forall d, In d ds1 -> d = DStep) /\ ds = ds1 ++ [DForce] ++ ds2 .
Proof.
  intros c st ast ds stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl; eauto; try discriminate.
  - destruct b' eqn:Eqb'.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev1 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists ds3; exists (ds4 ++ ds2). split; auto.
      rewrite app_comm_cons. rewrite app_assoc. simpl in Heq. rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev2 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (ds1 ++ ds3); exists ds4. split.
      * intros d H. apply in_app_or in H as [Hds1 | Hds3]; auto.
        eapply ideal_eval_final_bit_false in Hev1; [| eapply Hds1]. auto.
      * rewrite <- app_assoc. simpl in Heq. rewrite Heq. reflexivity.
  - (* IF non-speculative *)
    simpl in Hev. destruct (beval st be) eqn:Eqbe.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * simpl in Heq. rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * simpl in Heq. rewrite Heq. reflexivity.
  - (* IF speculative *)
    exists []; exists ds. split; simpl.
    + intros d H; destruct H.
    + reflexivity.
Qed.

(** * Conjectures for the proof of ideal_relative_secure *)

Conjecture ideal_eval_bit_deterministic :
  forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, b, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, b, ds)> =[ c ]=> <(stt2, astt2, bt2, os2 )> ->
    bt1 = bt2.

Conjecture ideal_eval_no_spec : forall c st ast ds stt astt bt os,
  (forall d, In d ds -> d = DStep) ->
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  <((c, st, ast ))> -->*^os <((skip, stt, astt))>.

Conjecture ideal_prefix_dirs :
  forall c st1 st2 ast1 ast2 b1 b2 ds1 ds2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
  prefix ds1 ds2 ->
  |-i <(st1, ast1, b1, ds1)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
  |-i <(st2, ast2, b2, ds2)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
  ds1 = ds2.

Conjecture ideal_exec_split_by_dirs : forall c st ast b ds stt astt bt os ds1 ds2,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  ds = ds1 ++ ds2 ->
  exists cm stm astm bm os1 os2,
    <((c, st, ast, b))> -->i*_ds1^^os1 <((cm, stm, astm, bm))> /\
    |-i <(stm, astm, bm, ds2)> =[ cm ]=> <(stt, astt, bt, os2)> /\
    os = os2++os1.

Conjecture ideal_exec_split : forall c st ast ds stt astt os ds1 ds2,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  (forall d, In d ds1 -> d = DStep) ->
  ds = ds1 ++ [DForce] ++ ds2 ->
  exists cm1 stm1 astm1 cm2 stm2 astm2 os1 os2 os3,
    <((c, st, ast, false))> -->i*_ds1^^os1 <((cm1, stm1, astm1, false))>  /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os2 <((cm2, stm2, astm2, true))> /\
    |-i <(stm2, astm2, true, ds2)> =[ cm2 ]=> <(stt, astt, true, os3)> /\
    os = os3 ++ os2 ++ os1.

Conjecture ideal_eval_small_step_no_spec : forall c st ast ds ct stt astt bt os,
    <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
    (forall d, In d ds -> d = DStep) ->
    <((c, st, ast ))> -->*^os <((ct, stt, astt))>.

(* HIDE: Probably this conjecture needs more assumptions on the starting states *)
Conjecture ideal_one_step_obs : forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2,
  <((c, st1, ast1, false))> -->i_[DForce]^^os1 <((ct, stt1, astt1, true))> ->
  <((c, st2, ast2, false))> -->i_[DForce]^^os2 <((ct, stt2, astt2, true))> ->
  os1 = os2.

(** * Ultimate SLH Relative Secure *)

Lemma ideal_relative_secure : forall c st1 st2 ast1 ast2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  ideal_same_obs c st1 st2 ast1 ast2.
Proof.
  unfold ideal_same_obs. intros c st1 st2 ast1 ast2 Hsec
  ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  eapply ideal_eval_bit_deterministic in Hev1 as SameB; try eassumption. subst.
  destruct bt1 eqn:Eqbt1.
  - (* with speculation *)
    assert (Hlen: length os1 = length os2).
    { apply ideal_obs_length in Hev1, Hev2. congruence. }
    eapply ideal_dirs_split in Hev1 as L.
    destruct L as [ds1 [ds2 [Hds1 Heq] ] ].
    rewrite Heq in Hev1, Hev2.
    eapply ideal_exec_split in Hev1; eauto.
    destruct Hev1 as [cm1 [stm1 [astm1 [cm2 [stm2 [astm2 [os1_1 [os1_2 [os1_3 [Hsmall1 [Hone1 [Hbig1 Hos1] ] ] ] ] ] ] ] ] ] ] ].
    eapply ideal_exec_split in Hev2; eauto.
    destruct Hev2 as [cm1' [stm' [astm1' [cm2' [stm2' [astm2' [os2_1 [os2_2 [os2_3 [Hsmall2 [Hone2 [Hbig2 Hos2] ] ] ] ] ] ] ] ] ] ] ].
    (* SOONER: Following conjecture needs determinism on com of samll step evaluation, i.e. c ds can only step to a unique c'. *)
    assert (Conj1 : cm1 = cm1' /\ cm2 = cm2'). { admit. }
    destruct Conj1 as [L1 L2]; subst.
    apply ideal_eval_small_step_no_spec in Hsmall1, Hsmall2; auto.
    eapply gilles_lemma in Hbig1; eauto. subst.
    eapply Hsec in Hsmall1. eapply Hsmall1 in Hsmall2 as Hpre.
    eapply ideal_one_step_obs in Hone1; eauto. subst.
    apply prefix_eq_length; auto.
    do 2 rewrite app_assoc. apply prefix_app_end. apply Hpre.
  - (* without speculation *)
    assert (Hds: forall d, In d ds -> d = DStep).
    { intros; eapply ideal_eval_final_bit_false in Hev1; eauto. }
    apply ideal_obs_length in Hev1 as Hos1.
    apply ideal_obs_length in Hev2 as Hos2.
    rewrite Hos1 in Hos2.
    eapply ideal_eval_no_spec in Hev1; try assumption.
    eapply ideal_eval_no_spec in Hev2; try assumption.
    eapply Hsec in Hev1; eapply Hev1 in Hev2.
    apply prefix_eq_length; now auto.
Admitted.

Theorem ultimate_slh_relative_secure :
  forall c st1 st2 ast1 ast2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
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
