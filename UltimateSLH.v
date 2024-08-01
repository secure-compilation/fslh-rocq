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

Definition seq_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com) (c:com) (st1 st2:state) : Prop :=
  forall ast1 ast2,
    seq_obs_secure c st1 st2 ast1 ast2 ->
    spec_obs_secure (trans c) st1 st2 ast1 ast2.

(** * Ultimate Speculative Load Hardening *)

(* HIDE: With BOr cand do [be || "b" <> 0], but whatever can also do it with BAnd
Definition BOr b1 b2 := BNot (BAnd (BNot b1) (BNot b2)).
Notation "x || y"  := (BOr x y) (in custom com at level 80, left associativity). *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be && "b" = 0 then "b" := (be ? "b" : 1); ultimate_slh c1
                          else "b" := (be ? 1 : "b"); ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be && "b" = 0 do "b" := (be ? "b" : 1); ultimate_slh c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

Fixpoint observations (c:com) (ds:dirs) : obs :=
  match c with
  | <{{skip}}> => []
  | <{{x := e}}> => []
  | <{{c1; c2}}> => observations c2 ds ++ observations c1 ds
  | <{{if be then c1 else c2 end}}> => observations c2 ds ++ [OBranch false]
  | <{{while be do c end}}> => []
  | <{{x <- a[[i]]}}> => [OARead a 0]
  | <{{a[i] <- e}}> => [OAWrite a 0]
  end.

Lemma observations_fixed : forall c st ast ds stt astt os,
  unused "b" c ->
  st "b" = 1 ->
  <(st, ast, true, ds)> =[ ultimate_slh c ]=> <(stt, astt, true, os)> ->
  os = observations c ds.
Admitted.

Lemma gilles_lemma : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  <(st1, ast1, true, ds)> =[ ultimate_slh c ]=> <(stt1, astt1, true, os1)> ->
  <(st2, ast2, true, ds)> =[ ultimate_slh c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2 Hunused Hb1 Hb2 H1 H2.
  apply observations_fixed in H1; try auto.
  apply observations_fixed in H2; try auto. congruence.
Qed.

Reserved Notation
         "'|-ideal-' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      |-ideal- <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      |-ideal- <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      |-ideal- <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      |-ideal- <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      |-ideal- <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os2++os1)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-ideal- <(st, ast, b, ds)> =[ match beval st be && (negb b) with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      |-ideal- <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch (beval st be && (negb b))])>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-ideal- <(st, ast, true, ds)> =[ c1 ]=> <(st', ast', b', os1)> ->
      |-ideal- <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', os1++[OBranch false])>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      |-ideal- <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      |-ideal- <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      |-ideal- <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> if b then nth 0 (ast a) 0 else nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      |-ideal- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth 0 (ast a') 0; st, ast, true, [OARead a i])>
  | Ideal_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      |-ideal- <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> if b then upd 0 (ast a) n else upd i (ast a) n; ast, b, [OAWrite a i])>
  | Ideal_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      |-ideal- <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd 0 (ast a') n; ast, true, [OAWrite a i])>

  where "|-ideal- <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval c st ast b ds stt astt bb os).

Definition ideal_obs_secure c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-ideal- <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-ideal- <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Lemma relative_noninterference : forall c st1 st2 ast1 ast2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  seq_obs_secure c st1 st2 ast1 ast2 ->
  ideal_obs_secure c st1 st2 ast1 ast2.
Proof.
Admitted.

Definition ultimate_slh_bcc_prop (c: com) (ds :dirs) :Prop :=
  forall st ast (b: bool) st' ast' b' os,
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
    |-ideal- <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

Lemma ultimate_slh_bcc : forall c ds,
  ultimate_slh_bcc_prop c ds.
Proof.
  apply prog_size_ind. unfold ultimate_slh_bcc_prop.
  intros c ds IH st ast b st' ast' b' os Hunused Hstb Heval.
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
    + admit. (* needs ultimate_slh_flag lemma
      apply sel_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * prog_size_auto. *)
  (* IF *)
  - (* non-speculative *) 
    destruct (beval st <{{ be && "b" = 0 }}>) eqn:Eqnbe; inversion H10; 
    inversion H1; subst; clear H10; clear H1; simpl in *.
    + apply andb_true_iff in Eqnbe as [Eqnbe Temp].
      rewrite Hstb in Temp. destruct b'0 eqn:Hbit; [discriminate |]; clear Temp.
      apply IH in H11; try tauto.
      * replace (OBranch true) with (OBranch (beval st be && (negb b'0)))
          by (rewrite Eqnbe; rewrite Hbit; reflexivity).
        rewrite <- Hbit at 1. apply Ideal_If. subst. rewrite Eqnbe; simpl.
          rewrite Eqnbe in H11. rewrite t_update_same in H11.
          rewrite app_nil_r. apply H11.
      * prog_size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
    + (* analog to true case *) admit.
Admitted.

Theorem relative_secure_slh :
  forall c st1 st2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    relative_secure ultimate_slh c st1 st2.
Admitted. (* from relative noninterference + bcc *)


